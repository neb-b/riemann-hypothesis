module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.IsSmoothCharUnr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SatDict
section
noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory.C GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

private theorem hasSat_iff {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (π : CuspSub K n)
    (v : HeightOneSpectrum (𝓞 K)) (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (hτ : π.IsLocComp v τ)
    (B : Multiset ℂˣ) : (Cusp.cx π).sat v B ↔ GlobalTheory.LFun.HasSatGL v τ.ρ B := by
  refine ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  have hB' : GlobalTheory.LFun.HasSatGL v (π.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep K n).comp (locGL K n v)) τ.ρ τ.irred
    (fun f : LocSph.Maps π v τ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL v (n := n) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v τ hτ]; exact x.2)
  obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred
    ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ hB'').unique hB' ▸ hB''

private theorem isSpherical_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) :
    IsSpherical τ.ρ ↔ GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.LFun.KGL v (n := n)) ≠ ⊥ := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := K) v n
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.satDict :
    UpperTheory.ConvolutionTheory.Sph.SatDict := by
  refine ⟨1, Or.inl rfl, ?_⟩
  intro K _ _ _ n π v τ hτ
  have hτ' : π.IsLocComp v τ := hτ
  refine ⟨?_, fun hs => ?_, fun α hs hα => ?_⟩
  · rintro ⟨B, hB⟩
    exact (isSpherical_iff v τ).2 ((hasSat_iff π v τ hτ' B).1 hB).1
  · refine GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries
      ((GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness _).1 (Fin n) τ.V τ.ρ τ.smooth τ.irred) τ.irred ?_
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun h => hx ⟨h.1, iwahori_le_KO _ _ h.2⟩, hx0⟩
  · have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K v n τ.V τ.ρ α ⟨τ.irred, hs, hα⟩
    have e : (Finset.univ.val.map fun i => α i ^ (1 : ℤ)) = Finset.univ.val.map α := by simp
    rw [e]
    exact (hasSat_iff π v τ hτ' _).2 h
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof

namespace UpperTheory.ConvolutionTheory.Sph.UnramifiedSpherical

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem prin_irr {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (h : ∀ i j, χ j ≠ χ i * absPow k 1) : (prinSeries χ).IsIrreducible := by
  let x : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (χ i) (hχ i)
  have hx : ∀ i, (x i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (x i).1 = n := by simp [x, IrrGL.ofChar]
  have hnu : ∀ i j, x j ≠ (x i).nu 1 := fun i j e => by
    simp only [x, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
    exact h i j e
  have hnl : ∀ i j, ¬ (Segment.single (x i) (hx i)).Linked (Segment.single (x j) (hx j)) := fun i j =>
    GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx i) (hx j) (hnu i j) (hnu j i)
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (x i) (hx i)) x hd hnl
      (fun i => (single_spec (hx i)).2.1)
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
    (stdBlocks (fun i => (x i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (χ i))
  let q := multiProdEquiv (stdBlocks (fun i => (x i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (χ i) (hχ i))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
  have hMnt : Nontrivial (IndSp (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
      (piTensor fun i => detRep (Fin 1) (χ i))) := nontrivial_of_irreducible hM
  have hnt {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) (hW : Nontrivial W) : Nontrivial V := by
    letI := hW
    obtain ⟨S, f, hf⟩ := h
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  letI := hnt (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries
    (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) χ) hMnt
  have heq {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) [Nontrivial W] (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨e⟩ := heq (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv e hM

private theorem unr_ne {a b : ℂˣ} (h : (a : ℂ) ≠ (resCard k : ℂ) * b) : unrChar k b ≠ unrChar k a * absPow k 1 := by
  intro e
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have e' := congrArg (fun χ : kˣ →* ℂˣ => ((χ ϖ : ℂˣ) : ℂ)) e
  simp only [MonoidHom.mul_apply, Units.val_mul] at e'
  rw [unrChar_uniformizer k b hϖ, unrChar_uniformizer k a hϖ, val_absPow] at e'
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (resCard k : ℂ) ≠ 0 := by
    have : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
    exact_mod_cast (by positivity : (resCard k : ℝ) ≠ 0)
  rw [Complex.cpow_one, hn] at e'
  apply h
  rw [e']
  push_cast
  field_simp

private theorem sph_of_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {π : Representation ℂ (GL (Fin n) k) W} (e : ρ.Equiv π)
    (h : IsSpherical ρ) : IsSpherical π := by
  unfold IsSpherical IsSphericalFor at *
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv x, fun g => ?_, fun h1 =>
    h0 (e.toLinearEquiv.injective (by rw [h1, map_zero]))⟩
  have hint : e.toLinearEquiv (ρ (g : GL (Fin n) k) x) = π (g : GL (Fin n) k) (e.toLinearEquiv x) :=
    LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin n) k)) x
  have hg := hx g
  rw [← hint, hg, map_smul]

end UpperTheory.ConvolutionTheory.Sph.UnramifiedSpherical

theorem UpperTheory.ConvolutionTheory.Sph.unlSph :
    UpperTheory.ConvolutionTheory.Sph.UnlSph := by
  intro K _ _ n v τ α h hs
  have hq : (resCard (v.adicCompletion K) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) := by
    have := GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm K v
    exact_mod_cast this
  have hI := UnramifiedSpherical.prin_irr (k := v.adicCompletion K) (fun i => unrChar (v.adicCompletion K) (α i))
    (fun i => PositivityTheory.Rg.BcB.N3.Pus.isSmoothChar_unr (α i))
    (fun i j => UnramifiedSpherical.unr_ne (by rw [hq]; exact h i j))
  obtain ⟨e⟩ := hs.nonempty_equiv τ.irred hI
  exact UnramifiedSpherical.sph_of_equiv e (PositivityTheory.Rg.BcB.N3.Pse.iP_sph (k := v.adicCompletion K) α)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnrNorm
section
namespace UpperTheory.ConvolutionTheory.Sph

private theorem zpow_inj_of_absNorm {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : ℤ}
    (h : (Ideal.absNorm v.asIdeal : ℝ) ^ a = (Ideal.absNorm v.asIdeal : ℝ) ^ b) : a = b := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun e => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  have h3 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast h2
  exact zpow_right_injective₀ (by linarith) h3.ne' h

theorem unrNorm : UnrNorm := by
  intro F E _ _ _ _ _ v w σw l N hN hq a
  refine MonoidHom.ext fun x => ?_
  have h := hN.abs x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, _root_.GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm F v, _root_.GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm E w.1, hq] at h
  have h' := zpow_inj_of_absNorm v h
  have h'' := neg_injective h'
  simp only [MonoidHom.comp_apply, GlobalTheory.SmGL.unrChar_apply, h'']

end UpperTheory.ConvolutionTheory.Sph
end

