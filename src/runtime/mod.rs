#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

/// The scalar model type for all runtime geometry: verified rational numbers.
#[cfg(verus_keep_ghost)]
pub type RationalModel = Rational;

pub mod point2;
pub mod point3;
pub mod orient;
pub mod classification;
pub mod segment;
pub mod aabb;
pub mod polygon;
pub mod intersection3d;
pub mod segment_polygon;
