#![cfg_attr(not(feature = "std"), no_std)]

/// Edit this file to define custom logic or remove it if it is not needed.
/// Learn more about FRAME and the core library of Substrate FRAME pallets:
/// https://substrate.dev/docs/en/knowledgebase/runtime/frame

use codec::{Decode, Encode};
use frame_support::{decl_module, decl_storage, decl_event, decl_error, dispatch, traits::Get};
use frame_system::ensure_signed;
use frame_support::ensure;
use frame_support::StorageMap;
use frame_support::Parameter;
use sp_std::vec::Vec;
use sp_runtime::traits::StaticLookup;
use sp_runtime::traits::Bounded;
use sp_runtime::traits::AtLeast32BitUnsigned;
use sp_runtime::traits::One;
use sp_runtime::DispatchError;
use sp_io::hashing::blake2_128;
use frame_support::traits::Randomness; // https://crates.parity.io/frame_support/traits/trait.Randomness.html

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

pub type DNA = [u8; 16];

// `derive` may only be applied to structs, enums and unions
#[derive(Encode, Decode)]
pub struct Kitty{
    pub dna : DNA,
}

/// Configure the pallet by specifying the parameters and types on which it depends.
pub trait Trait: frame_system::Trait {
	/// Because this pallet emits events, it depends on the runtime's definition of an event.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
    type KittyIndex : Parameter + AtLeast32BitUnsigned + Bounded + Default + Copy;
    type Randomness : Randomness<Self::Hash>;
}

// The pallet's runtime storage items.
// https://substrate.dev/docs/en/knowledgebase/runtime/storage
decl_storage! {
	// A unique name is used to ensure that the pallet's storage items are isolated.
	// This name may be updated, but each pallet in the runtime must use a unique name.
	// ---------------------------------vvvvvvvvvvvvvv
	trait Store for Module<T: Trait> as TemplateModule {
		// Learn more about declaring storage items:
		// https://substrate.dev/docs/en/knowledgebase/runtime/storage#declaring-storage-items
		Something get(fn something): Option<u32>;
        /// The storage item for our proofs.
        /// It maps a proof to the user who made the claim and when they made it.
        /// If a proof has an owner and a block number, then we know that it has been claimed!
        /// Otherwise, the proof is available to be claimed.
        Proofs: map hasher(blake2_128_concat) Vec<u8> => (T::AccountId, T::BlockNumber);

        Kitties get(fn kitties) : map hasher(blake2_128_concat) T::KittyIndex => Option<Kitty>;

        KittiesCount get(fn kitties_count) : T::KittyIndex;

        KittyOwners get(fn kitty_owners) : map hasher(blake2_128_concat) T::KittyIndex => Option<T::AccountId>;

        // Kitty
	}
}

// Pallets use events to inform users when important changes are made.
// https://substrate.dev/docs/en/knowledgebase/runtime/events
decl_event!(
	pub enum Event<T> where
        AccountId = <T as frame_system::Trait>::AccountId,
        KittyIndex = <T as Trait>::KittyIndex
    {
		/// Event documentation should end with an array that provides descriptive names for event
		/// parameters. [something, who]
		SomethingStored(u32, AccountId),
        /// Event emitted when a proof has been claimed. [who, claim]
        ClaimCreated(AccountId, Vec<u8>),
        /// Event emitted when a claim is revoked by the owner. [who, claim]
        ClaimRevoked(AccountId, Vec<u8>),
        /// Event emitted when a claim is transferred by the owner. [who, whom, claim]
        ClaimTransferred(AccountId, AccountId, Vec<u8>),

        /// Placeholder event to mark KittyIndex as used Type Parameter, any type parameter has to
        /// be used once to make the rust compiler happy. see `rustc --explain E0392`. At the moment of writing 
        /// HelloKitty(KittyIndex) means nothing, but later it will be used to indicate that a new kitty has
        /// been created
        HelloKitty(AccountId, KittyIndex),
	}
);

// Errors inform users that something went wrong.
decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Error names should be descriptive.
		NoneValue,
		/// Errors should have helpful documentation associated with them.
		StorageOverflow,
        /// The proof has already been claimed.
        ProofAlreadyClaimed,
        /// The proof does not exist, so it cannot be revoked.
        NoSuchProof,
        /// The proof is claimed by another account, so caller can't revoke it.
        NotProofOwner,
        /// The proof is too large to consume.
        ProofTooLarge,
        /// Too many kitties.
        KittyOverflow,
        /// The index has ho associated kitty.
        InvalidKittyIndex,
        /// The offspring's dna must come from different parents.
        SelfReproductionNotAllowed,
	}
}

// Dispatchable functions allows users to interact with the pallet and invoke state changes.
// These functions materialize as "extrinsics", which are often compared to transactions.
// Dispatchable functions must be annotated with a weight and must return a DispatchResult.
decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// Errors must be initialized if they are used by the pallet.
		type Error = Error<T>;

		// Events must be initialized if they are used by the pallet.
		fn deposit_event() = default;

		/// An example dispatchable that takes a singles value as a parameter, writes the value to
		/// storage and emits an event. This function must be dispatched by a signed extrinsic.
		#[weight = 10_000 + T::DbWeight::get().writes(1)]
		pub fn do_something(origin, something: u32) -> dispatch::DispatchResult {
			// Check that the extrinsic was signed and get the signer.
			// This function will return an error if the extrinsic is not signed.
			// https://substrate.dev/docs/en/knowledgebase/runtime/origin
			let who = ensure_signed(origin)?;

			// Update storage.
			Something::put(something);

			// Emit an event.
			Self::deposit_event(RawEvent::SomethingStored(something, who));
			// Return a successful DispatchResult
			Ok(())
		}

		/// An example dispatchable that may throw a custom error.
		#[weight = 10_000 + T::DbWeight::get().reads_writes(1,1)]
		pub fn cause_error(origin) -> dispatch::DispatchResult {
			let _who = ensure_signed(origin)?;

			// Read a value from storage.
			match Something::get() {
				// Return an error if the value has not been set.
				None => Err(Error::<T>::NoneValue)?,
				Some(old) => {
					// Increment the value read from storage; will error in the event of overflow.
					let new = old.checked_add(1).ok_or(Error::<T>::StorageOverflow)?;
					// Update the value in storage with the incremented result.
					Something::put(new);
					Ok(())
				},
			}
		}

        /// Allow a user to claim ownership of an unclaimed proof.
        #[weight = 10_000]
        fn create_claim(origin, proof: Vec<u8>) {
            // Check proof length sanity
            ensure!(proof.len() <= 42, Error::<T>::ProofTooLarge);
            // Check that the extrinsic was signed and get the signer.
            // This function will return an error if the extrinsic is not signed.
            // https://substrate.dev/docs/en/knowledgebase/runtime/origin
            let sender = ensure_signed(origin)?;

            // Verify that the specified proof has not already been claimed.
            ensure!(!Proofs::<T>::contains_key(&proof), Error::<T>::ProofAlreadyClaimed);

            // Get the block number from the FRAME System module.
            let current_block = <frame_system::Module<T>>::block_number();

            // Store the proof with the sender and block number.
            Proofs::<T>::insert(&proof, (&sender, current_block));

            // Emit an event that the claim was created.
            Self::deposit_event(RawEvent::ClaimCreated(sender, proof));
        }

        /// Allow the owner to revoke the claim.
        #[weight = 10_000]
        fn revoke_claim(origin, proof: Vec<u8>) {
            // Check that the extrinsic was signed and get the signer.
            // This function will return an error if the extrinsic is not signed.
            // https://substrate.dev/docs/en/knowledgebase/runtime/origin
            let sender = ensure_signed(origin)?;

            // Verify that the specified proof has been claimed.
            ensure!(Proofs::<T>::contains_key(&proof), Error::<T>::NoSuchProof);

            // Get owner of the claim.
            let (owner, _) = Proofs::<T>::get(&proof);

            // Verify that sender of the current call is the claim owner.
            ensure!(sender == owner, Error::<T>::NotProofOwner);

            // Remove claim from storage.
            Proofs::<T>::remove(&proof);

            // Emit an event that the claim was erased.
            Self::deposit_event(RawEvent::ClaimRevoked(sender, proof));
        }

        /// Allow the owner to transfer the claim.
        #[weight = 10_000]
        fn transfer_claim(origin, proof: Vec<u8>, dest: <T::Lookup as StaticLookup>::Source) {
            // Check that the extrinsic was signed and get the signer.
            // This function will return an error if the extrinsic is not signed.
            // https://substrate.dev/docs/en/knowledgebase/runtime/origin
            let sender = ensure_signed(origin)?;
            let receiver = T::Lookup::lookup(dest)?;

            // Verify that the specified proof has been claimed.
            ensure!(Proofs::<T>::contains_key(&proof), Error::<T>::NoSuchProof);

            // Get owner of the claim.
            let (owner, current_block) = Proofs::<T>::get(&proof);

            // Verify that sender of the current call is the claim owner.
            ensure!(sender == owner, Error::<T>::NotProofOwner);

            // Verify that receiver of the current call is not the sender.
            ensure!(receiver != sender, Error::<T>::ProofAlreadyClaimed);

            // Transfer claim ownership to receiver
            // https://stackoverflow.com/questions/59140724/what-is-the-difference-between-traitt-and-traitt
            // Proofs::<T>::insert(&proof, (&receiver, current_block));
            // <Proofs<T>>::insert(&proof, (&receiver, current_block));
            // <Proofs::<T>>::insert(&proof, (&receiver, current_block));
            Proofs::<T>::insert(&proof, (&receiver, current_block));

            // Emit an event that the claim was transferred.
            Self::deposit_event(RawEvent::ClaimTransferred(sender, receiver, proof));
        }

        /// Let there be kitties!
        #[weight = 10_000]
        fn create_kitty(origin) {
            // Check that the extrinsic was signed and get the signer.
            // This function will return an error if the extrinsic is not signed.
            // https://substrate.dev/docs/en/knowledgebase/runtime/origin
            let owner = ensure_signed(origin)?;
            let kid = Self::new_kid()?;
            let dna = Self::rand_dna(&owner);
            let kitty = Kitty{dna}; // https://doc.rust-lang.org/book/ch05-01-defining-structs.html
            Self::register_kitty(kid, kitty, &owner);
            Self::deposit_event(RawEvent::HelloKitty(owner, kid));
        }
	}
}

// another way to do it:
// impl<T> Module<T> where T: Trait {
// reference: https://stackoverflow.com/questions/54504026/how-do-i-provide-an-implementation-of-a-generic-struct-in-rust
impl<T: Trait> Module<T> {
    // this fn is prone to integer overflow, in which case an error shall be returned
    // therefore the return type should be Result<T, E>
    fn new_kid() -> sp_std::result::Result<T::KittyIndex, DispatchError> {
        let kid = Self::kitties_count();
        ensure!(kid < T::KittyIndex::max_value(), <Error<T>>::KittyOverflow);
        Ok(kid)
    }
}

impl<T: Trait> Module<T> {
    fn rand_dna(owner : &T::AccountId) -> DNA {
        (
            T::Randomness::random_seed(), 
            &owner, 
            <frame_system::Module<T>>::extrinsic_index()
        )
          .
            using_encoded(blake2_128)
    }
    fn combine_dna(mask : DNA, x: DNA, y : DNA) -> DNA {
        let mut dna = [0u8; 16];
        for i in 0..mask.len() {
            dna[i] = (mask[i] & x[i]) | (mask[i] & y[i]);
        }
        dna
    }
    fn do_breed(owner : &T::AccountId, x : T::KittyIndex, y : T::KittyIndex) -> sp_std::result::Result<T::KittyIndex, DispatchError>{
        ensure!(x != y, <Error<T>>::SelfReproductionNotAllowed);
        let x = Self::kitties(x).ok_or(<Error<T>>::InvalidKittyIndex)?;
        let y = Self::kitties(y).ok_or(<Error<T>>::InvalidKittyIndex)?;
        let m = Self::rand_dna(&owner);
        let i = Self::new_kid()?;
        let d = Self::combine_dna(m, x.dna, y.dna);
        Self::register_kitty( i, Kitty{dna: d}, owner);
        Ok(i)
    }
}

impl<T : Trait> Module<T> {
    // Error: not implemented
    // rustc --explain E0202
    // type KittyIndex = T::KittyIndex;

    fn _link_kid_to_owner(kid : T::KittyIndex, owner : &T::AccountId) {
        <KittyOwners::<T>>::insert::<>(kid, &owner);
    }

    fn _link_kid_to_kitty(kid : T::KittyIndex, kitty : Kitty) {
        <Kitties::<T>>::insert::<>(kid, kitty);
    }

    fn _increment_kitties_count(kid : T::KittyIndex) {
        <KittiesCount::<T>>::put::<>(kid + One::one::<>());
    }

    fn register_kitty(
        kid : T::KittyIndex,
        kitty : Kitty,
        owner : &T::AccountId)
    {
       Self::_link_kid_to_owner::<>(kid, &owner);
       Self::_link_kid_to_kitty::<>(kid, kitty);
       Self::_increment_kitties_count::<>(kid);
    }

}
