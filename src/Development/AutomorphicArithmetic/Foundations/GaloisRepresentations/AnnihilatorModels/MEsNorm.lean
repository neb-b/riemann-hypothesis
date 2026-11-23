module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.FrobKill
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelValueIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteFlatCoverModelIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Gal.crystallineComparison.Mod.esNorm_of (hG : UpperTheory.Gal.crystallineComparison.Mod.EsGen) : UpperTheory.Gal.crystallineComparison.Mod.EsNorm := by
  intro p _ D R _ _ _ _ b N h3 hcop hp r w j c hw hu hj hc hm M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, hst₀, hgs, hgt, hfgs, hegs, hfgt, hegt, hiso₀, htj₀, huniv₀⟩ :=
    hG p D R b N h3 hcop hp r w j c hw hu hj hc hm M
  obtain ⟨Y, s, i, hio, hid, hi, hfs, hnorm, hflat, hnoeth, hext⟩ :=
    NormCover.exists_finite_normal_model p D R b N hp M Y₀ s₀ gs hfgs hegs hgs
  obtain ⟨t, hit, ht, hft⟩ := GlobalTheory.ExtT.exists_finite_extension p D R b N h3 hcop hp r w j c hw hu hj hc hm M
    Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst₀ hgs hgt hfgs hegs hfgt hegt hiso₀ htj₀ Y s i hio hid hi hfs hnorm hflat
    hnoeth hext
  have hred : AlgebraicGeometry.IsReduced Y :=
    isReduced_normalModel_of_generic p D R b N hp M Y₀ s₀ gs hgs hegs Y s i hio hi hflat hext
  have hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y) := fun y => by
    have := hnorm y
    let A := Y.presheaf.stalk y
    refine (isDomain_iff_noZeroDivisors_and_nontrivial A).2 ⟨⟨?_⟩, inferInstance⟩
    intro a b hab
    let I : Ideal A := Ideal.span {a}
    let J : Ideal A := I ⊔ I.annihilator
    -- The sum of an ideal and its annihilator is faithful in a reduced ring.
    have : FaithfulSMul A J := Module.annihilator_eq_bot.mp <| by
      change J.annihilator = ⊥
      rw [show J = I ⊔ I.annihilator from rfl, Submodule.annihilator_sup, eq_bot_iff]
      intro z hz
      have hzz : z * z = 0 := Submodule.mem_annihilator.mp hz.2 z hz.1
      have hz0 : z = 0 := IsNilpotent.eq_zero ⟨2, by simpa only [pow_two] using hzz⟩
      simpa using hz0
    obtain ⟨s, hs, hreg⟩ := Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul (I := J)
    obtain ⟨u, v, hv, rfl⟩ := Ideal.mem_span_singleton_sup.mp hs
    have hva : v * a = 0 := Submodule.mem_annihilator.mp hv a (Ideal.mem_span_singleton_self a)
    -- The fraction (u * a) / (u * a + v) is integral because it is idempotent.
    let F := FractionRing A
    let d : nonZeroDivisors A := ⟨u * a + v, hreg⟩
    let e : F := IsLocalization.mk' F (u * a) d
    let f := algebraMap A F
    have hf : Function.Injective f := IsFractionRing.injective A F
    have he : e * f (u * a + v) = f (u * a) := IsLocalization.mk'_spec F (u * a) d
    have hu : IsUnit (f (u * a + v)) := IsLocalization.map_units F d
    have hidem : e * e = e := by
      apply hu.mul_right_cancel
      apply hu.mul_right_cancel
      have hmul : f (u * a) * f (u * a + v) = f (u * a) * f (u * a) := by
        rw [← map_mul, ← map_mul, mul_add, mul_assoc u a v, mul_comm a v, hva, mul_zero, add_zero]
      calc e * e * f (u * a + v) * f (u * a + v)
          = (e * f (u * a + v)) * (e * f (u * a + v)) := by ring
        _ = f (u * a) * f (u * a) := by rw [he]
        _ = f (u * a) * f (u * a + v) := hmul.symm
        _ = e * f (u * a + v) * f (u * a + v) := by rw [he]
    have hint : IsIntegral A e := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
      simp [Polynomial.eval₂_sub, pow_two, hidem]
    obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
    have hcc : c * c = c := hf (by rw [map_mul, hc, hidem])
    have hcs : c * (u * a + v) = u * a := hf (by rw [map_mul, hc, he])
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
    · have hc1 : c = 1 := h.mul_left_cancel (by rw [hcc, _root_.mul_one])
      have hs : u * a + v = u * a := by simpa [hc1] using hcs
      right
      apply (mem_nonZeroDivisors_iff_left.mp hreg) b
      rw [hs, _root_.mul_assoc, hab, mul_zero]
    · have hc0 : c = 0 := h.mul_right_eq_zero.mp (by rw [sub_mul, _root_.one_mul, hcc, sub_self])
      have hua : u * a = 0 := by simpa [hc0] using hcs.symm
      left
      apply (mem_nonZeroDivisors_iff_right.mp hreg) a
      rw [hua, zero_add, mul_comm, hva]
  obtain ⟨o, ⟨ms⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X Y M.s s M.univ
  have hpt := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X Y M.s t M.univ
  rw [ht] at hpt
  obtain ⟨o', ⟨mt⟩⟩ := hpt
  subst hi
  subst hit
  obtain ⟨m, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ ms₀ ms
  obtain ⟨m', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ mt₀ mt
  obtain ⟨ψ, hiso, hcomm⟩ := PIsogExt.exists_isPIsog_extend p D R b N h3 hcop j c hc Y₀ Y i _ _ hio hid hnoeth
    hnorm hdom o o' o₀ o₀' m m' ψ₀ hiso₀
  refine ⟨Y, s, t, o, o', ms, mt, ψ, ht.symm, hfs, hft, hnorm, hflat, hiso, ?_, ?_⟩
  · exact isTj_of_objMap_factor p D R b N r w j Y₀ Y i _ _ o o' o₀ o₀' m m' ψ₀ ψ hcomm hext htj₀
  · exact existsUnique_of_openImmersion p D R b N h3 hcop r w j c M Y₀ Y i (i ≫ s) s _ _ o o' o₀ o₀' m m'
      ψ₀ ψ hio rfl hcomm hext huniv₀
