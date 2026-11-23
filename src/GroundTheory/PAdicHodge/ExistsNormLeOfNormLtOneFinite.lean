module

public import Mathlib
public import GroundTheory.PAdicHodge.WAKummerEps
public import GroundTheory.PAdicHodge.FundamentalSeqLog
public import GroundTheory.PAdicHodge.FundamentalSeqBCris
public import GroundTheory.PAdicHodge.ACrisFrobFixed
public import GroundTheory.PAdicHodge.BCrisRegularFinal
public import GroundTheory.PAdicHodge.BdRInvariants
public import GroundTheory.PAdicHodge.AxLemma
public import GroundTheory.PAdicHodge.FundamentalSeqSurj

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

section Span

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {K}

end Span

section Contradiction

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv 𝒪♭ p)

theorem gal_smul_untilt_iterate_of_eq_mul {ε x : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    {σ : Gal(PadicAlgCl p/K)} {a : ℤ_[p]} (h : tiltGal σ x = x * epsPow hε a) (m : ℕ) :
    σ • ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) *
      ((PreTilt.untilt (φi^[m] ε) : 𝒪) : ℂ_[p]) ^ (PadicInt.toZModPow m a).val := by
  rw [← coe_untilt_iterate_tiltGal, h, iterate_frobSymm_mul, map_mul, untilt_iterate_epsPow,
    MulMemClass.coe_mul, SubmonoidClass.coe_pow]



end Contradiction

end GroundTheory.PAdicHodge
