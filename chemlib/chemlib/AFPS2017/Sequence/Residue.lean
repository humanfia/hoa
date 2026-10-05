/-!
# Residue specification

A residue specification records generic identity, chirality, and protection
metadata. These fields expose no empirical values or claims.

Source references:

* Mijalis et al., Nature Chemical Biology (2017),
  DOI `10.1038/nchembio.2318` (`afps2017.main`).
* Public Supplementary Information,
  SHA-256 `f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e`
  (`afps2017.supplement`).
-/

namespace AFPS2017.Sequence

/-- Type-safe metadata describing a residue without assigning empirical values. -/
structure ResidueSpec (Identity Chirality Protection : Type) : Type where
  chirality : Chirality
  identity : Identity
  protection : Protection

end AFPS2017.Sequence
