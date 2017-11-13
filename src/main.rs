// Rusty Coins
// (CCO) 2017 - Richard van Roy

#[macro_use]
extern crate serde_derive;
extern crate bincode;
extern crate rand;
extern crate sha2;
extern crate ed25519_dalek;

use std::collections::HashMap;

use bincode::{serialize, Infinite};
use rand::OsRng;
use sha2::Sha512;
use ed25519_dalek::Keypair;
use ed25519_dalek::PublicKey;
use ed25519_dalek::Signature as EDSignature;

/// A wallet contains the public- and private key of a 'rusty coin' user.
/// Money can be transfered to a user's public key and transactions are
/// signed using a users private key.
struct Wallet {
    public_key:  [u8; 32],
    private_key: [u8; 32],
}

impl Wallet {
    /// Generates a new user with random keys
    fn new() -> Wallet {
        let mut cspring: OsRng = OsRng::new().unwrap();
        let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
        Wallet {
            public_key: keypair.public.to_bytes(),
            private_key: keypair.secret.to_bytes()
        }
    }
}

/// A structure containing a transaction
#[derive(Serialize, Clone, Debug)]
struct Transaction {
    /// The owner of the transaction, i.e. the person sending credits.
    owner: [u8; 32],
    /// The signatures of outputs of other transactions that have not been spend yet.
    inputs: Vec<Input>,
    /// The public_keys of the users where credits need to be send to and the amount
    /// of credits.
    outputs: Vec<Output>,
    /// The amount of change to refund when transaction completes.
    change: isize,
    /// Before a transaction can be added to the chain it must first be signed using
    /// a users private_key.
    signature: Signature
}

impl Transaction {

    /// Sends credits from a users wallet to the the user with the public_key in public_key_receiver.
    fn new(chain: &mut Chain, wallet: &Wallet, public_key_receiver: [u8; 32], amount: isize) -> Transaction {
        // Gather input blocks ...
        let (inputs, change) = chain.collect_until(wallet.public_key, amount);

        let transaction = Transaction {
            owner: wallet.public_key.clone(),
            inputs: inputs.clone(),
            change: change,
            outputs: vec![Output {
                public_key_receiver: public_key_receiver,
                amount: amount
            }],
            signature: Signature::Unsigned
        };

        transaction
    }

    /// Use a users wallet to sign a transaction.
    fn sign(&mut self, wallet: &Wallet) {
        let keypair = Keypair::from_bytes(&wallet.public_key, &wallet.private_key);
        let serialized = serialize(self, Infinite).unwrap();
        self.signature = Signature::Signed(keypair.sign::<Sha512>(&serialized).to_bytes().to_vec());
    }

    /// Create a new, unsigned version of a transaction. Used to test the validity of a signature.
    fn unsigned(&self) -> Transaction {
        let mut clone = (*self).clone();
        clone.signature = Signature::Unsigned;
        clone
    }

    /// Validate this transaction
    fn validate(&self, chain: &Chain, root_user_public_key: [u8; 32]) -> Validation {
        let public_key = PublicKey::from_bytes(&self.owner);
        let first = match self.signature {
            Signature::Signed(ref s) => {
                let signature = EDSignature::from_bytes(s);
                let serialized = serialize(&self.unsigned(), Infinite).unwrap();
                if !public_key.verify::<Sha512>(&serialized, &signature) {
                    // Transaction has an invalid signature ...
                    Validation::InvalidSignature
                } else {
                    for r in self.inputs.iter() {
                        let t = chain.transactions.get(&r.signature);
                        match t { 
                            None => Validation::Valid,
                            Some(ref t) => match t.validate(chain, root_user_public_key) {
                                Validation::Valid => Validation::Valid,
                                // Transaction has an invalid input somewhere down the tree ...
                                _ => Validation::InvalidInputs
                            }
                        };
                    } 
                    // Transaction is valid ...
                    Validation::Valid
                }
            }
            // Transaction no signature ...
            Signature::Unsigned => Validation::Unsigned
        };

        match first {
            Validation::Valid => {
                // Check if all amounts ar non zero ...
                if self.outputs.iter().map(|x| x.amount).any(|x| x==0) {
                    Validation::InvalidAmount
                } else {
                    // Check if there are enough credits ...
                    let total_in = chain.worth(self.owner);
                    let total_out = self.outputs.iter().fold(0, |sum, x| sum + x.amount);
                    if total_in >= total_out
                        || self.owner == root_user_public_key // root user can make money
                    {
                        Validation::Valid
                    } else {
                        // There weren't enough credits associated with this user ...
                        Validation::NotEnoughCredits
                    }
                }
            },
            _ => first
        }

    }

    /// Returns all outputs beloning to public_key in this transaction
    fn outputs_for(&self, public_key: [u8; 32]) -> Vec<(Vec<u8>, Output)> {
        match self.signature {
            Signature::Signed(ref s) => {
                let outputs = &self.outputs;
                outputs.into_iter()
                    .filter(|i| i.public_key_receiver == public_key)
                    .map(|i| ((*s).clone(), i.clone()))
                    .collect()
            }
            Signature::Unsigned => Vec::new()
        }
    }
}

/// A blockchain of transactions
struct Chain {
    transactions: HashMap<Vec<u8>, Transaction>,
    root_user: Wallet
}

impl Chain {
    /// Create a new blockchain with a genesis transaction of total_credits.
    /// These's credits are transfered to the lucky_public_key.
    fn new(total_credits: isize, lucky_public_key: [u8; 32]) -> Chain {
        let root_user = Wallet::new();
        // Create the genesis transaction. We must do this by hand because we do
        // not have any inputs.
        let mut genesis = Transaction {
            owner: root_user.public_key,
            inputs: Vec::new(),
            change: 0,
            outputs: vec![Output {
                public_key_receiver: lucky_public_key,
                amount: total_credits
            }],
            signature: Signature::Unsigned
        };
        // Sign the transaction
        genesis.sign(&root_user);
        let mut transactions = HashMap::new();
        match genesis.signature {
            Signature::Signed(ref s) => {
                transactions.insert((*s).clone(), genesis.clone());
                Chain {
                    transactions: transactions,
                    root_user: root_user
                }
            }
            // This should not happen (unreachable)
            Signature::Unsigned => panic!("unreachable")
        }
    }

    /// Check a transaction for validity, if valid returns Validation::Valid and add
    /// it to the chain. Else return the reason why it is invalid.
    fn add(&mut self, transaction: &Transaction) -> Validation {
        // Check if this transaction was already added ...
        for t in self.transactions.iter() {
            if let Signature::Signed(ref s) = transaction.signature {
                if t.0 == s {
                    return Validation::Double;
                }
            }
        }

        match transaction.signature {
            Signature::Signed(ref s) => {
                let validation = transaction.validate(self, self.root_user.public_key);
                match validation {
                    Validation::Valid => {
                        // Transaction is valid, add it to the chain ...
                        self.transactions.insert((*s).clone(), transaction.clone());

                        // If there is any change, transfer it back to oneself ...
                        if transaction.change > 0 {
                            // Because it is the last transaction added to the input list
                            // this is the one for which change must be given.
                            let mut new_root = Transaction {
                                owner: self.root_user.public_key.clone(),
                                inputs: Vec::new(),
                                change: 0,
                                outputs: Vec::new(),
                                signature: Signature::Unsigned
                            };
                            new_root.sign(&self.root_user);
                            if let Signature::Signed(ref s) = new_root.signature {
                                let mut change_transaction = Transaction {
                                    owner: self.root_user.public_key.clone(),
                                    inputs: vec![Input::new((*s).clone())],
                                    outputs: vec![Output {
                                        public_key_receiver: transaction.owner.clone(),
                                        amount: transaction.change
                                    }],
                                    change: 0,
                                    signature: Signature::Unsigned
                                };
                                change_transaction.sign(&self.root_user);
                                self.add(&change_transaction);
                            }
                        }

                        Validation::Valid
                    } _ => validation
                }
            }
            // Transaction was not signed ... (unreachable)
            Signature::Unsigned => Validation::Unsigned
        }
    }

    /// Returns a list of all inputs that are spendable by a user with a speicific
    /// public_key.
    fn spendable_inputs(&self, public_key: [u8; 32]) -> Vec<Transaction> {
        let transactions = &self.transactions;
        // Create a list of all inputs in the entire chain ...
        let mut all_inputs = Vec::new();
        for (_, t) in transactions {
            for i in &t.inputs {
                all_inputs.push(&i.signature);
            }
        }

        // Checks if a transaction was already spend ...
        let was_spend = |transaction: &Transaction| {
            match transaction.signature {
                Signature::Signed(ref s) => {
                    all_inputs.contains(&s)
                }
                // Invalid,... so spend
                Signature::Unsigned => true
            }
        };

        // The total amount of credits to be send to public_key
        let amount_for_public_key = |t: &Transaction| {
            let mut total = 0;
            for o in t.outputs.iter() {
                if o.public_key_receiver == public_key {
                    total += o.amount;
                }
            }
            total
        };

        // Filter transaction to those that are spendable ...
        transactions.into_iter()
            .filter(|&(_, ref t)| amount_for_public_key(t) != 0 && !was_spend(t))
            .map(|(_, t)| t.clone())
            .collect()
    }

    /// Collect inputs until there total worth is more then the amount given.
    fn collect_until(&self, public_key: [u8; 32], amount: isize) -> (Vec<Input>, isize) {
        let mut total = 0;
        let mut inputs: Vec<Input> = Vec::new();
        let transactions = self.spendable_inputs(public_key);
        for t in transactions.iter() {
            for (s, o) in t.outputs_for(public_key) {
                if amount > total {
                    total += o.amount;
                    inputs.push(Input::new(s));
                }
            }
        }
        (inputs, total-amount)
    }

    /// Returns the total amount of credits associated with a public_key.
    fn worth(&self, public_key: [u8; 32]) -> isize {
        let mut total = 0;
        let transactions = self.spendable_inputs(public_key);
        for t in transactions.iter() {
            for (_, o) in t.outputs_for(public_key) {
                total += o.amount;
            }
        }
        total
    }
}

#[derive(Serialize, Clone, Debug)]
enum Signature {
    Signed(Vec<u8>),
    Unsigned
}

#[derive(Serialize, Clone, Debug)]
struct Input {
    signature: Vec<u8>,
}

impl Input {
    fn new(signature: Vec<u8>) -> Input {
        Input {
            signature
        }
    }
}

#[derive(Serialize, Clone, Debug)]
struct Output {
    public_key_receiver: [u8; 32],
    amount: isize
}

#[derive(Debug)]
enum Validation {
    Valid,
    NotEnoughCredits,
    Unsigned,
    InvalidSignature,
    InvalidInputs,
    InvalidAmount,
    Double
}

#[cfg(test)]
mod tests {

    use super::*;
    
    #[test]
    fn transfering_money() {
        // Create 3 users ...
        let user1 = Wallet::new();
        let user2 = Wallet::new();
        let user3 = Wallet::new();

        // Grand user1 all the total_credits (100)
        let mut chain = Chain::new(100, user1.public_key);

        // Transfer half of it to user2 ...
        // There are 100 credits contained in one block. They will be split up by creating
        // another transaction worth 50 credits a change and assigning it back to user1
        let mut transaction = Transaction::new(&mut chain, &user1, user2.public_key, 50); {
            // sign the transaction
            transaction.sign(&user1);
            // add transaction to the chain
            chain.add(&transaction);
        }
        

        // Transfer another 40 to user2 ...
        let mut transaction = Transaction::new(&mut chain, &user1, user2.public_key, 40); {
            chain.worth(user1.public_key);
            transaction.sign(&user1);
            chain.add(&transaction);
        }

        // Have user two send all but one credit to user3 ...
        let mut transaction = Transaction::new(&mut chain, &user2, user3.public_key, 89); {
            transaction.sign(&user2);
            chain.add(&transaction);
        }
        
        // Check if users have the expected amount of money ...
        assert!(chain.worth(user1.public_key) == 10);
        assert!(chain.worth(user2.public_key) == 1);
        assert!(chain.worth(user3.public_key) == 89);
   }

    #[test]
    fn too_little_money() {
        let user1 = Wallet::new();
        let user2 = Wallet::new();

        let mut chain = Chain::new(100, user1.public_key);

        // User1 has total_credits (100), transfer 101 to user2
        let mut transaction = Transaction::new(&mut chain, &user1, user2.public_key, 101);
        transaction.sign(&user1);
        let validation = chain.add(&transaction);

        // There shouldn't be enough money 
        assert!(match validation { Validation::NotEnoughCredits => true, _ => false });
       
        // Check if users still have the expected amount of money ...
        assert!(chain.worth(user1.public_key) == 100);
        assert!(chain.worth(user2.public_key) == 0);
    }

    #[test]
    fn wrong_signature() {
        let user1 = Wallet::new();
        let user2 = Wallet::new();
        let mut chain = Chain::new(100, user1.public_key);

        let mut transaction = Transaction::new(&mut chain, &user1, user2.public_key, 1);
        // Sign with wrong wallet
        transaction.sign(&user2);
        let validation = chain.add(&transaction);

        // Signature should be invalid ...
        assert!(match validation { Validation::InvalidSignature => true, _ => false });

        // Check if users still have the expected amount of money ...
        assert!(chain.worth(user1.public_key) == 100);
        assert!(chain.worth(user2.public_key) == 0);

    }

    #[test]
    fn no_signature() {
        let user1 = Wallet::new();
        let user2 = Wallet::new();
        let mut chain = Chain::new(100, user1.public_key);

        let transaction = Transaction::new(&mut chain, &user1, user2.public_key, 1);
        let validation = chain.add(&transaction);

        // Transaction was not signed and should be invalid ...
        assert!(match validation { Validation::Unsigned => true, _ => false });

        // Check if users still have the expected amount of money ...
        assert!(chain.worth(user1.public_key) == 100);
        assert!(chain.worth(user2.public_key) == 0);
    }

    #[test]
    fn double_spend() {
        let user1 = Wallet::new();
        let user2 = Wallet::new();
        let mut chain = Chain::new(100, user1.public_key);

        let mut transaction = Transaction::new(&mut chain, &user1, user2.public_key, 1);
        transaction.sign(&user1);

        // Try addingg the same transaction twice
        chain.add(&transaction);
        let validation = chain.add(&transaction);

        // Transaction should be marked as double ...
        assert!(match validation { Validation::Double => true, _ => false });

        // Check if users still have the expected amount of money ...
        assert!(chain.worth(user1.public_key) == 99);
        assert!(chain.worth(user2.public_key) == 1);
    }
}

fn main() {
    // Transfer 100 credits to user ...
    let me = Wallet::new();
    let you = Wallet::new();
    let mut chain = Chain::new(100, me.public_key);
    let mut transaction = Transaction::new(&mut chain, &me, you.public_key, 100);
    transaction.sign(&me);
    chain.add(&transaction);
    let worth = chain.worth(you.public_key);

    println!("You just received: {} rusty coins! (Don't spend them all at once)\nPlease run the tests with: 'cargo test'", worth);
}

