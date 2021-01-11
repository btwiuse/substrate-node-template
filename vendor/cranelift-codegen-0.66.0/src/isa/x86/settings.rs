//! x86 Settings.

use crate::settings::{self, detail, Builder};
use core::fmt;

// Include code generated by `cranelift-codegen/meta/src/gen_settings.rs:`. This file contains a
// public `Flags` struct with an impl for all of the settings defined in
// `cranelift-codegen/meta/src/isa/x86/settings.rs`.
include!(concat!(env!("OUT_DIR"), "/settings-x86.rs"));

#[cfg(test)]
mod tests {
    use super::{builder, Flags};
    use crate::settings::{self, Configurable};

    #[test]
    fn presets() {
        let shared = settings::Flags::new(settings::builder());

        // Nehalem has SSE4.1 but not BMI1.
        let mut b0 = builder();
        b0.enable("nehalem").unwrap();
        let f0 = Flags::new(&shared, b0);
        assert_eq!(f0.has_sse41(), true);
        assert_eq!(f0.has_bmi1(), false);

        let mut b1 = builder();
        b1.enable("haswell").unwrap();
        let f1 = Flags::new(&shared, b1);
        assert_eq!(f1.has_sse41(), true);
        assert_eq!(f1.has_bmi1(), true);
    }
    #[test]
    fn display_presets() {
        // Spot check that the flags Display impl does not cause a panic
        let shared = settings::Flags::new(settings::builder());

        let b0 = builder();
        let f0 = Flags::new(&shared, b0);
        let _ = format!("{}", f0);

        let mut b1 = builder();
        b1.enable("nehalem").unwrap();
        let f1 = Flags::new(&shared, b1);
        let _ = format!("{}", f1);

        let mut b2 = builder();
        b2.enable("haswell").unwrap();
        let f2 = Flags::new(&shared, b2);
        let _ = format!("{}", f2);
    }
}
