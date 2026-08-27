/-!
# Provenance for reported AFPS2017 data

This module implements the empirical-data (E) boundary specified by the sanitized
sources `afps2017.analytics.contract:question` and
`afps2017.evidence.boundary:question`. A reported datum records where a payload
came from; it does not establish the payload as chemical truth.

In particular, this module intentionally provides no coercion from reported data
and no operation that transforms a payload while claiming to preserve provenance.
-/

namespace AFPS2017.Analytics

/-- (E) A stable reference to the public source of a reported datum. -/
structure SourceRef : Type where
  doi : String
  locator : String
  url : String
  contentHash : String

/--
(E) A payload paired with its source. This is a data record, not evidence for an
arbitrary proposition about the payload.
-/
structure ReportedDatum (α : Type u) : Type u where
  source : SourceRef
  value : α

/--
(E) A reference into the public AFPS2017 supplementary information associated
with DOI `10.1038/nchembio.2318`.
-/
def afps2017Supplement (locator : String) : SourceRef :=
  { doi := "10.1038/nchembio.2318"
    locator := locator
    url :=
      "https://media.springernature.com/original/springer-static/esm/art%3A10.1038%2Fnchembio.2318/MediaObjects/41589_2017_BFnchembio2318_MOESM199_ESM.pdf"
    contentHash := "f7baa2cd59141ec38d95c9980e60117b596a9a78a9f4cbd4ae4e2cd4a2c8044e" }

end AFPS2017.Analytics
