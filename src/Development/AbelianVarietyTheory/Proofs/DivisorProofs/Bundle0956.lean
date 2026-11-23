module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominators
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.BoundedDen

theorem den_factorization_le (p : ℕ) [Fact p.Prime] (q : ℚ) (M : ℕ) (hM : 0 < M) (k : ℤ) (e : ℕ)
    (h : q * ((M : ℚ) * (p : ℚ) ^ e) = k) (ℓ : ℕ) (hℓ : ℓ ≠ p) :
    q.den.factorization ℓ ≤ M.factorization ℓ := by
  have hp : p.Prime := Fact.out
  have hN : ((M * p ^ e : ℕ) : ℚ) ≠ 0 := by
    have : 0 < M * p ^ e := Nat.mul_pos hM (pow_pos hp.pos e)
    exact_mod_cast this.ne'
  have hq : q = Rat.divInt k ((M * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast at hN ⊢
    rw [eq_div_iff hN]; exact h
  have hd : q.den ∣ M * p ^ e := by
    have := Rat.den_dvd k ((M * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hle := (Nat.factorization_le_iff_dvd q.den_nz (Nat.mul_pos hM (pow_pos hp.pos e)).ne').2 hd ℓ
  rw [Nat.factorization_mul hM.ne' (pow_pos hp.pos e).ne', Nat.factorization_pow, hp.factorization] at hle
  simpa [Finsupp.single_apply, Ne.symm hℓ] using hle

end GlobalTheory.LKCx.BoundedDen

namespace GlobalTheory.LKCx.BoundedDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  intro p _ G β x t hx L f hf h₁
  obtain ⟨Ω, Ω', hΩ, hΩ', hmem⟩ := exists_compact_toAfF p G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  let b := Module.finBasis ℚ G.C
  let b' := b.baseChange (AfP p)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i =>
    hΩ.image (IsModuleTopology.continuous_of_linearMap (b'.coord i))
  choose m hm0 hm using fun i => GlobalTheory.DenAway.den_bounded_of_isCompact p _ (hcpt i)
  obtain ⟨M', hM'0, hM'⟩ := GlobalTheory.DenAway.den_bounded_of_isCompact p Ω' hΩ'
  refine ⟨(∏ i, m i) * M', Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0, fun y hy ℓ hℓ => ⟨fun i => ?_, ?_⟩⟩
  · have hval : b'.coord i (inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        algebraMap ℚ (AfP p) (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) := by
      simp only [inC, b', RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Module.Basis.coord_apply,
        Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    obtain ⟨k, e, hk⟩ := hm i (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) (by rw [← hval]; exact ⟨_, (hmem y hy).1, rfl⟩)
    have h1 := den_factorization_le p _ (m i) (hm0 i) k e hk ℓ hℓ
    have hd : m i ∣ (∏ j, m j) * M' := (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).mul_right _
    exact h1.trans ((Nat.factorization_le_iff_dvd (hm0 i).ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 hd ℓ)
  · have e0 : ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ := Units.val_inv_eq_inv_val _
    obtain ⟨k, e, hk⟩ := hM' _ (hmem y hy).2
    rw [e0]
    have h1 := den_factorization_le p _ M' hM'0 k e hk ℓ hℓ
    exact h1.trans ((Nat.factorization_le_iff_dvd hM'0.ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 (dvd_mul_left _ _) ℓ)

end GlobalTheory.LKCx.BoundedDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPartFullEqKilled
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CuspMult.CutFull

open GlobalTheory.CuspMult GlobalTheory.CuspMult.EqCut

theorem mem_killed_union {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (I I' : Set (MonoidAlgebra ℂ H)) (v : X) : v ∈ killed ρ (I ∪ I') ↔ v ∈ killed ρ I ∧ v ∈ killed ρ I' := by
  simp only [mem_killed, Set.mem_union, or_imp, forall_and]

theorem mem_partFull_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ) (T : MMap M) :
    T ∈ partFull θ M J χ SF a ↔ T ∈ Mult θ M J χ ∧ ∀ Q d R, Hecke₂ V J χ SF Q d R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = a Q d * T v x := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_partFull_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ partFull θ M (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF a = GlobalTheory.CuspMult.allMaps θ M ⊓ GlobalTheory.CuspMult.killed (GlobalTheory.CuspMult.finRep M) (GlobalTheory.CuspMult.eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim ∪ {x | ∃ (Q : Pl D.host.E) (d : List ℤ) (B : Finset (GfC V)), Hecke₂ V (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF Q d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ∧ x = ∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 (a Q d)}) := by
  intro D V S θ M β L G _ _ eG c P SF a hs hQ hlift
  have h0 := good_hecke_eq_killed θ M β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim hs hQ hlift
  have h1 : ∀ T : MMap M, T ∈ goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ↔
      T ∈ allMaps θ M ∧ T ∈ killed (finRep M) (eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
    intro T
    rw [← Submodule.mem_inf, ← h0, Submodule.mem_inf, mem_hPart]
    exact ⟨fun h => ⟨h, fun p => p.elim⟩, fun h => h.1⟩
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_killed_union, ← and_assoc, ← h1, mem_partFull_iff]
  refine and_congr_right fun hg => ?_
  rw [mem_killed]
  constructor
  · rintro ⟨-, hh⟩ x ⟨Q, d, B, hB, rfl⟩
    refine (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
    have := hh Q d _ hB v x
    rw [Finset.sum_map] at this
    simp only [one_mul]
    exact this
  · intro hk
    have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hg.1
    refine ⟨(GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).2 ⟨hm.aut, hm.cusp, fun v k hkk x => ?_, hm.equiv, hm.cont⟩, ?_⟩
    · exact hasType_flag1 P (F := T v) (fun k hk h => hm.lev v k hk h) k hkk x
    · intro Q d R hR v x
      classical
      have hf : ∀ γ ∈ R, γ ∈ GfC V := by
        obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, h⟩ := hR
        exact fun γ hγ => (h.1 γ hγ).1
      obtain ⟨B, rfl⟩ : ∃ B : Finset (GfC V), B.map ⟨Subtype.val, Subtype.val_injective⟩ = R :=
        ⟨R.subtype (· ∈ GfC V), Finset.subtype_map_of_mem hf⟩
      have := (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).1 (hk _ ⟨Q, d, B, hR, rfl⟩) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.CutFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.FlagGS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sgn_mul_self (p a : ℕ) : ((sgn p a : ℝ) : ℂ) * ((sgn p a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem diag_of_upper {r : ℕ} (s : Fin r → ℂ) (hs : ∀ a, s a * s a = 1) (b : Matrix (Fin r) (Fin r) ℂ)
    (hb : b.BlockTriangular id) (h : bᵀ * diagonal s * b.map (starRingEnd ℂ) = diagonal s) :
    ∃ t : Fin r → ℝ, b = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
  have hs0 : ∀ a, s a ≠ 0 := fun a h0 => by simpa [h0] using hs a
  have hss : diagonal s * diagonal s = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [diagonal_mul_diagonal]; simp [hs]
  have h1 : (diagonal s * bᵀ * diagonal s) * b.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.mul_assoc (diagonal s), Matrix.mul_assoc (diagonal s), h, hss]
  have hc : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    rw [Matrix.map_apply, hb hca, map_zero]
  letI : Invertible (b.map (starRingEnd ℂ)) := invertibleOfLeftInverse _ _ h1
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hc
  rw [Matrix.inv_eq_left_inv h1] at hinv
  have hoff : ∀ a c, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with hlt | hlt
    · have := hinv (i := c) (j := a) hlt
      rw [mul_diagonal, diagonal_mul, transpose_apply] at this
      simpa [hs0] using this
    · exact hb hlt
  have hd : b = diagonal fun a => b a a := by
    ext a c
    by_cases hac : a = c
    · subst hac; simp
    · rw [diagonal_apply_ne _ hac, hoff a c hac]
  have hn : ∀ a, ‖b a a‖ = 1 := by
    intro a
    have h2 := congrFun (congrFun h a) a
    rw [hd, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal] at h2
    simp only [diagonal_apply_eq] at h2
    have h3 : b a a * starRingEnd ℂ (b a a) = 1 := by
      apply mul_left_cancel₀ (hs0 a)
      linear_combination h2
    have h4 := congrArg norm h3
    rw [norm_mul, Complex.norm_conj, norm_one] at h4
    nlinarith [norm_nonneg (b a a)]
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  calc
    b = diagonal (fun a => b a a) := hd
    _ = diagonal (fun a => Complex.exp ((Complex.arg (b a a) : ℂ) * Complex.I)) := by
      congr 1
      funext a
      have harg := Complex.norm_mul_exp_arg_mul_I (b a a)
      rw [hn a] at harg
      simpa using harg.symm

theorem exp_keeps {r : ℕ} {H Z : Matrix (Fin r) (Fin r) ℂ} (hH : H * H = 1) (hZ : Zᴴ * H + H * Z = 0) :
    (NormedSpace.exp Z)ᴴ * H * NormedSpace.exp Z = H := by
  have hu : IsUnit H.det := Matrix.isUnit_det_of_left_inverse hH
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : Zᴴ = H * (-Z) * H⁻¹ := by
    have h1 : Zᴴ * H = -(H * Z) := eq_neg_of_add_eq_zero_left hZ
    rw [mul_neg, ← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem conj_keeps {r : ℕ} (s : Fin r → ℝ) (g : Matrix (Fin r) (Fin r) ℂ)
    (h : gᴴ * diagonal (fun a => (s a : ℂ)) * g = diagonal fun a => (s a : ℂ)) :
    gᵀ * diagonal (fun a => (s a : ℂ)) * g.map (starRingEnd ℂ) = diagonal fun a => (s a : ℂ) := by
  have h2 := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, diagonal_map (map_zero (starRingEnd ℂ)), Complex.conj_ofReal] at h2
  have e : gᴴ.map (starRingEnd ℂ) = gᵀ := by
    ext a c; simp [conjTranspose_apply]
  rwa [e] at h2

theorem gram_schmidt_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  intro E _ _ _ r X
  have hdom : ∀ y, IsUnitFr X y → y ∈ X.dom := fun y hy => ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.orth_mem_dom X hy
  refine ⟨hdom, fun x hx => ?_, fun y hy b hb hyb => ?_,
    fun x hx b hb => ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun y hy γ hγ τ => ?_, fun y hy Z hZ τ => ?_,
    fun la P y hy b hb hP => ?_⟩
  · have hb := FrameDegreeData.bOf_mem X hx
    refine ⟨rmul x (FrameDegreeData.bOf X x), FrameDegreeData.ortho_bOf X hx, fun τ => ((mat (FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ),
      fun τ => ?_, ?_⟩
    · have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      letI := Matrix.invertibleOfIsUnitDet _ hu
      refine ⟨?_, fun a c hca => Matrix.blockTriangular_inv_of_blockTriangular (FrameDegreeData.upper_of_bor X hb τ) hca⟩
      exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
    · funext τ
      have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      exact (Matrix.mul_nonsing_inv_cancel_right _ (mat x τ) hu).symm
  · have h : ∀ τ : X.Ψ, ∃ t : Fin r → ℝ, mat b τ = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
      intro τ
      have h1 := hyb τ
      rw [show mat (rmul y b) τ = mat y τ * mat b τ from rfl, FrameDegreeData.gram_mul, hy τ] at h1
      exact diag_of_upper _ (fun a => sgn_mul_self _ _) _ (FrameDegreeData.upper_of_bor X hb τ) h1
    choose t ht using h
    exact ⟨t, funext fun τ => ht τ⟩
  · rw [ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ]
    exact hy τ
  · rw [show mat (rmul y (expFr Z)) τ = mat y τ * NormedSpace.exp (mat Z τ) from rfl, FrameDegreeData.gram_mul, hy τ]
    refine conj_keeps _ _ (exp_keeps ?_ (hZ τ))
    rw [diagonal_mul_diagonal]
    simp only [sgn_mul_self]
    exact diagonal_one
  · have hx := hdom y hy
    unfold Data.pnorm
    rw [hP, norm_mul]
    have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
      unfold bchar
      simp only [norm_prod, norm_zpow]
    rw [hbc, mul_comm (∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i) ‖P y‖, mul_assoc, ← Finset.prod_mul_distrib]
    conv_rhs => rw [← mul_one ‖P y‖]
    congr 1
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [FrameDegreeData.ratio_rmul X y hx hb τ i,
      FrameDegreeData.factor_eq _ _ (norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ i)) (norm_nonneg _), norm_div,
      ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy, ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy,
      div_one, Real.one_rpow]

end GlobalTheory.FlagGS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLi
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaDeriv

theorem decay_majorant {F : Type} [Field F] [NumberField F] {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ C : ℝ, ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
      ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨C, c, hcs, hc0, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]

theorem schr_line_add (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (t h : ℝ) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (M (t + h)) Φ = GlobalTheory.WeilM.schr ψ (M t) (GlobalTheory.WeilM.schr ψ (M h) Φ) := by
  rw [schr_schr, _root_.GlobalTheory.ThetaTransform.symV_realLine_eq_zero F N hF M hM t h, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add (f := _)]

theorem exists_deriv_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {M : ℝ →+ VA F N} (hM : IsRealLine M) {Φ : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) :
    ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N), ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨f', hf'⟩ := _root_.GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero F N ψ hF hψ M hM f g hg
    exact ⟨_, Submodule.subset_span ⟨f', g, hg, rfl⟩, hf'⟩
  | zero =>
    refine ⟨0, zero_mem _, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (0 : (Fin N → AF F) → ℂ) z) = fun _ => 0 := by
      funext s; simp [GlobalTheory.WeilM.schr]
    rw [e]
    exact hasDerivAt_const 0 0
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨Φ', h1m, h1d⟩ := h1
    obtain ⟨Ψ', h2m, h2d⟩ := h2
    refine ⟨Φ' + Ψ', add_mem h1m h2m, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (Φ + Ψ) z) =
        fun s => GlobalTheory.WeilM.schr ψ (M s) Φ z + GlobalTheory.WeilM.schr ψ (M s) Ψ z := by
      funext s; simp [GlobalTheory.WeilM.schr, mul_add]
    rw [e]
    exact (h1d z).add (h2d z)
  | smul c Φ _ h =>
    obtain ⟨Φ', hm, hd⟩ := h
    refine ⟨c • Φ', Submodule.smul_mem _ c hm, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (c • Φ) z) = fun s => c * GlobalTheory.WeilM.schr ψ (M s) Φ z := by
      funext s; simp [GlobalTheory.WeilM.schr]; ring
    rw [e]
    exact (hd z).const_mul c

theorem hasDerivAt_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    {Φ Φ' : (Fin N → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0)
    (z : Fin N → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) (t - t) := by
    have e : (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) = fun h =>
        ψ (z ⬝ᵥ (M t).2 + ⅟(2 : AF F) * ((M t).1 ⬝ᵥ (M t).2)) * GlobalTheory.WeilM.schr ψ (M h) Φ (z + (M t).1) := by
      funext h
      rw [schr_line_add hF ψ hM]
      rfl
    rw [e, sub_self]
    exact (hd (z + (M t).1)).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

end GlobalTheory.ThetaDeriv


open GlobalTheory.ThetaDeriv in
theorem GlobalTheory.ThetaTransform.hasDerivAt_heisV_line : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N),
      ∀ w, HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  intro F _ _ N _ ψ hF hψ Φ hΦ M hM
  obtain ⟨Φ', hΦ'm, hΦ'd⟩ := exists_deriv_schr hF ψ hψ hM hΦ
  refine ⟨Φ', hΦ'm, fun w => ?_⟩
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := decay_majorant hF (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ := decay_majorant hF (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr hF ψ hM hΦ'd (rat ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacterStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  first | exact @GlobalTheory.KSp.GaussMain.hasGauss_herm | exact GlobalTheory.KSp.GaussMain.hasGauss_herm | (intros; apply GlobalTheory.KSp.GaussMain.hasGauss_herm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeKeepsAndCommutes
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeOffLevel

variable {D : D7}

theorem sep_of_offS {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hS : OffS D S Q) (hP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) : PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q := by
  obtain ⟨x, hx, hQ⟩ := hS _ hP
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  refine ⟨fun h => hQ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl (h ▸ hx'), fun h => ?_⟩
  obtain ⟨c, hc, e⟩ := h _ hx'
  exact hQ c (e.trans ((D.sp.cm.fixed _).2 ⟨x, rfl⟩)) hc

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_mul : ∀ k ∈ Lev.levG V β L, ∀ k' ∈ Lev.levG V β L,
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  intro k hk k' hk'
  unfold Lev.levChi
  rw [MonoidHom.map_mul, ← Units.val_mul]
  exact congrArg Units.val ((levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {Rp : Finset (GA D V)}

theorem hasType_heckeLin (hB : Lev.IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q)
    (h : Hecke₂ V (Lev.levG V β L : Set (GA D V)) (Lev.levChi V β L) S Q d Rp) {Φ : GA D V → ℂ}
    (hΦ : Lev.HasType V β L Φ) : Lev.HasType V β L (heckeLin V Rp Φ) :=
  GlobalTheory.SphericalOps.level_heckeLin levChi_mul
    (fun e f _ hi => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 Q e f hi hN hP).2.2) h hΦ

end GlobalTheory.HeckeOffLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one : GlobalTheory.EtC.C2 := by
  first | (exact @GlobalTheory.EtC.etC_c2) | (exact GlobalTheory.EtC.etC_c2) | (intros; apply GlobalTheory.EtC.etC_c2  <;> assumption)
end

