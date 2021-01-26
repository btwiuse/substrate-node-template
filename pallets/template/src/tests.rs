use crate::{Error, mock::*};
use frame_support::{assert_ok, assert_noop};
use super::*;

#[test]
fn it_works_for_default_value() {
	new_test_ext().execute_with(|| {
		// Dispatch a signed extrinsic.
		assert_ok!(TemplateModule::do_something(Origin::signed(1), 42));
		// Read pallet storage and assert an expected result.
		assert_eq!(TemplateModule::something(), Some(42));
	});
}

#[test]
fn correct_error_for_none_value() {
	new_test_ext().execute_with(|| {
		// Ensure the expected error is thrown when no value is present.
		assert_noop!(
			TemplateModule::cause_error(Origin::signed(1)),
			Error::<Test>::NoneValue
		);
	});
}

#[test]
fn create_claim_works() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        assert_ok!(
            TemplateModule::create_claim(Origin::signed(1), claim.clone())
        );
        assert_eq!(
            Proofs::<Test>::get(&claim),
            (1, frame_system::Module::<Test>::block_number())
        );
	});
}

#[test]
fn create_existing_claim_fails() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        let _ = TemplateModule::create_claim(Origin::signed(1), claim.clone());
        assert_noop!(
            TemplateModule::create_claim(Origin::signed(1), claim.clone()),
            Error::<Test>::ProofAlreadyClaimed
        );
	});
}

#[test]
fn revoke_claim_works() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        let _ = TemplateModule::create_claim(Origin::signed(1), claim.clone());
        assert_ok!(
            TemplateModule::revoke_claim(Origin::signed(1), claim.clone())
        );
	});
}

#[test]
fn revoke_non_existent_claim_fails() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        assert_noop!(
            TemplateModule::revoke_claim(Origin::signed(1), claim.clone()),
            Error::<Test>::NoSuchProof
        );
	});
}

#[test]
fn revoke_non_claim_owner_fails() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        let _ = TemplateModule::create_claim(Origin::signed(1), claim.clone());
        assert_noop!(
            TemplateModule::revoke_claim(Origin::signed(2), claim.clone()),
            Error::<Test>::NotProofOwner
        );
	});
}

#[test]
fn transfer_claim_works() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        let _ = TemplateModule::create_claim(Origin::signed(1), claim.clone());
        assert_ok!(
            TemplateModule::transfer_claim(Origin::signed(1), claim.clone(), 42)
        );
        assert_eq!(
            Proofs::<Test>::get(&claim),
            (42, frame_system::Module::<Test>::block_number())
        );
        assert_noop!(
            TemplateModule::revoke_claim(Origin::signed(1), claim.clone()),
            Error::<Test>::NotProofOwner
        );
	});
}

#[test]
fn transfer_non_owned_claim_fails() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        let _ = TemplateModule::create_claim(Origin::signed(1), claim.clone());
        assert_noop!(
            TemplateModule::transfer_claim(Origin::signed(2), claim.clone(), 42),
            Error::<Test>::NotProofOwner
        );
	});
}

#[test]
fn transfer_non_existent_claim_fails() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0, 1];
        assert_noop!(
            TemplateModule::transfer_claim(Origin::signed(1), claim.clone(), 42),
            Error::<Test>::NoSuchProof
        );
	});
}

#[test]
fn create_huge_claim_fails() {
	new_test_ext().execute_with(|| {
        let claim: Vec<u8> = vec![0; 43];
        assert_noop!(
            TemplateModule::create_claim(Origin::signed(1), claim.clone()),
            Error::<Test>::ProofTooLarge
        );
	});
}

/// L2Q5
/// here are kitty related tests
#[test]
fn create_kitty_ok() {
}
