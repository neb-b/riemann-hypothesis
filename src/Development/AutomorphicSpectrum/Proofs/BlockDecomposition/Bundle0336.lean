module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.AdelicGLn
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactor
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.Segments

theorem exists_coatom_ge_of_hasFiniteLength {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {P : Representation ℂ G V} (hfl : HasFiniteLength P) (S : Subrepresentation P) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation P, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfl
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ G) P.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation P) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := P)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

theorem cosocle_quotient_of_quotient : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q)
    (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  intro G V W X _ _ _ _ _ _ _ σ P Q hc hfl f hf hQ
  obtain ⟨-, f0, hf0, hco⟩ := hc
  have hne : Representation.IntertwiningMap.ker P Q f ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨v, rfl⟩ := hf x
    have hv : v ∈ (⊤ : Subrepresentation P) := trivial
    rw [← h] at hv
    exact hx hv
  obtain ⟨C, hC, hle⟩ := exists_coatom_ge_of_hasFiniteLength hfl _ hne
  have hk : ∀ v : V, f v = 0 → f0 v = 0 := by
    intro v hv
    have h1 : v ∈ Representation.IntertwiningMap.ker P Q f := hv
    have h2 : v ∈ C := hle h1
    rw [hco C hC] at h2
    exact h2
  let e := LinearMap.quotKerEquivOfSurjective f.toLinearMap hf
  let gl : X →ₗ[ℂ] W :=
    (LinearMap.ker f.toLinearMap).liftQ f0.toLinearMap (fun v hv => hk v hv) ∘ₗ e.symm.toLinearMap
  have hgl : ∀ v : V, gl (f v) = f0 v := by
    intro v
    have h1 : e.symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [gl, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    rfl
  refine ⟨⟨gl, fun h => ?_⟩, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := hf x
    have h2 : Q h (f v) = f (P h v) := by
      have := congrArg (fun m => m v) (f.isIntertwining' h)
      exact this.symm
    have h3 : f0 (P h v) = σ h (f0 v) := congrArg (fun m => m v) (f0.isIntertwining' h)
    simp only [LinearMap.comp_apply]
    rw [h2, hgl, hgl, h3]
  · intro w
    obtain ⟨v, rfl⟩ := hf0 w
    exact ⟨f v, hgl v⟩

end GlobalTheory.CompanionTheory.Segments
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg Matrix

namespace GlobalTheory.CompanionTheory.SegNu

theorem exists_ne_zero_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra h
  push_neg at h
  haveI := hi
  refine (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective ?_)
  show (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

theorem eq_smul_of_eigenvector {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ} {w : V}
    (hw : w ≠ 0) (hc : π z w = c • w) (v : V) : π z v = c • v := by
  haveI := hi
  let E : Subrepresentation π :=
    { toSubmodule := LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : π z v = c • v := by
          simpa [sub_eq_zero] using hv
        have h1 : π z (π g v) = π g (π z v) := by
          rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
        simp [sub_eq_zero, h1, hv'] }
  have hE : E ≠ ⊥ := fun h => hw (by
    have h1 : w ∈ E.toSubmodule := by
      show w ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      simp [sub_eq_zero, hc]
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1)
  have hT : E = ⊤ := (eq_bot_or_eq_top E).resolve_left hE
  have h2 : v ∈ E.toSubmodule := by
    rw [hT]
    exact Submodule.mem_top
  have h3 : v ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V)) := h2
  simpa [sub_eq_zero] using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_scalar {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (ha : IsAdmissible π) (hi : π.IsIrreducible) {z : GL (Fin n) k} (hz : ∀ g, z * g = g * z) :
    ∃ ω : ℂ, ∀ v, π z v = ω • v := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr hi
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show π 1 v = v
        simp
      inv_mem' := fun {a} ha => by
        have ha' : π a v = v := ha
        show π a⁻¹ v = v
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set (GL (Fin n) k)) := ha.1 v
  let K : Subgroup (GL (Fin n) k) := S ⊓ KO k (Fin n)
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) Set.inter_subset_right
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hKo hKc
  have hvK : v ∈ fixed π K := fun h => by
    have h' : π (h : GL (Fin n) k) v = v := h.2.1
    simpa using h'
  haveI : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  have hst : ∀ u ∈ fixed π K, π z u ∈ fixed π K := fun u hu h => by
    have hu' := hu h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hu' ⊢
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply, hu']
  let T : Module.End ℂ (fixed π K) := (π z).restrict hst
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have h1 : π z (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have h2 : (w : V) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  exact ⟨c, eq_smul_of_eigenvector hi hz h2 h1⟩

theorem eq_zero_of_nu_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hd : 0 < x.1) {s : ℝ}
    (hs : x.nu (s : ℂ) = x) : s = 0 := by
  have h1 := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k (s : ℂ)) (isSmoothChar_absPow _)
  rw [IrrGL.of_rep] at h1
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 (h1.symm.trans (hs.trans (IrrGL.of_rep x).symm))
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let z : GL (Fin x.1) k := GeneralLinearGroup.scalar (Fin x.1) ϖ
  have hz : ∀ g, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = ϖ ^ x.1 := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨ω, hω⟩ := exists_scalar (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr hz
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr x.2.rep.irr
  have hω0 : ω ≠ 0 := fun e => hv (by
    have h2 : x.rep z⁻¹ (x.rep z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hω, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have h3 := LinearMap.congr_fun (φ.isIntertwining' z) v
  have hLv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h4 : φ.toLinearEquiv (((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) • x.rep z v) = x.rep z (φ.toLinearEquiv v) := by
    have h5 : φ.toLinearEquiv ((twist x.rep (detChar _ (absPow k (s : ℂ)))) z v) = x.rep z (φ.toLinearEquiv v) := h3
    rwa [twist_apply, detChar_apply, hdet] at h5
  rw [hω, hω, map_smul, map_smul, smul_smul] at h4
  have h6 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) * ω = ω := smul_left_injective ℂ hLv h4
  have h7 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ hω0 (h6.trans (one_mul ω).symm)
  have h8 : ((absPow k (s : ℂ) ϖ : ℂˣ) : ℂ) ^ x.1 = 1 := by
    rw [← h7, map_pow, Units.val_pow_eq_pow_val]
  rw [val_absPow_ofReal] at h8
  have h9 : (nabs k ϖ ^ s) ^ x.1 = 1 := by exact_mod_cast h8
  have hpos : 0 < nabs k ϖ := nabs_pos' k ϖ
  have h10 : nabs k ϖ ^ s = 1 := (pow_eq_one_iff_of_nonneg (Real.rpow_nonneg hpos.le s) hd.ne').1 h9
  have hne : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have h11 := congrArg Real.log h10
  rw [Real.log_rpow hpos, Real.log_one] at h11
  exact (mul_eq_zero.1 h11).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hpos hne)

theorem nu_natCast_inj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ)
    (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  intro k _ _ _ _ hA x hx a b h
  have h1 : x.nu (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) = x := by
    have h2 := congrArg (fun y => IrrGL.nu y (-(b : ℂ))) h
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
    rw [← h2]
    congr 1
    push_cast
    ring
  have h3 := eq_zero_of_nu_eq hA x hx.1 h1
  exact_mod_cast sub_eq_zero.1 h3

end GlobalTheory.CompanionTheory.SegNu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FineStep

theorem isSubquotient_subQuot_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {J : Representation ℂ G V} (S R : Subrepresentation J) : IsSubquotient (subQuot S R) J := by
  refine GlobalTheory.SmGL.IsSubquotient.trans (σ := S.toRepresentation) ?_ ?_
  · refine GlobalTheory.SmGL.IsSubquotient.of_surjective
      ⟨(Submodule.comap S.toSubmodule.subtype R.toSubmodule).mkQ, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Submodule.mkQ_surjective _
  · refine GlobalTheory.SmGL.IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Subtype.val_injective

theorem nonempty_equiv_of_jhMult_eq_one :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J →
      jhMult T J = 1 →
      (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible →
        IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  intro G V W _ _ _ _ _ T J hT hfin hJ hall
  have hstep : ∀ {P Q : Subrepresentation J}, Q ⋖ P → GlobalTheory.JHMult.Step T P Q := fun {P Q} h =>
    GlobalTheory.JHMult.step_iff.mp
      (hall _ (subQuot P Q) (GlobalTheory.SmGL.isIrreducible_subQuot h) (isSubquotient_subQuot_self P Q))
  have hwf : WellFounded ((· < ·) : Subrepresentation J → Subrepresentation J → Prop) := by
    haveI : IsArtinian (MonoidAlgebra ℂ G) J.asModule :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (show IsFiniteLength (MonoidAlgebra ℂ G) J.asModule from hfin)).2
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := J)).toOrderEmbedding.ltEmbedding.wellFounded
      wellFounded_lt
  have hne : (⊥ : Subrepresentation J) ≠ ⊤ := by
    intro h
    haveI : Subsingleton V := ⟨fun a b => by
      have ha : a ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      have hb : b ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      rw [← h] at ha hb
      rw [(Submodule.mem_bot ℂ).mp ha, (Submodule.mem_bot ℂ).mp hb]⟩
    have h0 := GlobalTheory.SmGL.jhMult_of_subsingleton hT J
    rw [hJ] at h0
    exact one_ne_zero h0
  have hirr : J.IsIrreducible := by
    show IsSimpleOrder (Subrepresentation J)
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun S => ?_ }
    by_contra hS
    obtain ⟨hS0, hS1⟩ := not_or.mp hS
    obtain ⟨A, ⟨hA0, hAS⟩, hAmin⟩ := hwf.has_min {A | ⊥ < A ∧ A ≤ S}
      ⟨S, show ⊥ < S ∧ S ≤ S from ⟨bot_lt_iff_ne_bot.mpr hS0, le_rfl⟩⟩
    obtain ⟨B, hB, hBmin⟩ := hwf.has_min {B | S < B}
      ⟨⊤, show S < ⊤ from lt_top_iff_ne_top.mpr hS1⟩
    have hcA : (⊥ : Subrepresentation J) ⋖ A := ⟨hA0, by
      intro c hc hcA
      exact hAmin c (show ⊥ < c ∧ c ≤ S from ⟨hc, hcA.le.trans hAS⟩) hcA⟩
    have hSB : S < B := hB
    have hcB : S ⋖ B := ⟨hSB, by
      intro c hc hcB
      exact hBmin c (show S < c from hc) hcB⟩
    have hocc : GlobalTheory.SmGL.OccursTimes T J 2 := by
      have := GlobalTheory.JHMult.occurs_of_finset (σ := T) (ρ := J) (r := 2) Finset.univ ![A, B] ![⊥, S]
        (by simp [Fin.forall_fin_two, hSB.le]) (by simp [Fin.forall_fin_two, hAS])
        (by simp [Fin.forall_fin_two, hstep hcA, hstep hcB])
      simpa using this
    have h2 : ((2 : ℕ) : ℕ∞) ≤ GlobalTheory.SmGL.jhMult T J := by
      unfold GlobalTheory.SmGL.jhMult
      exact le_iSup₂_of_le 2 hocc le_rfl
    rw [hJ] at h2
    have h21 : ¬ ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [ENat.natCast_le_natCast]
      omega
    exact h21 (by simpa using h2)
  exact hall V J hirr (GlobalTheory.SmGL.IsSubquotient.refl J)

end GlobalTheory.CompanionTheory.FineStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaFin

theorem exists_unip_mul_lev {R : Type} [CommRing R] (r s : ℕ) (P : GL (Fin (r + s)) R)
    (h1 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (P : Matrix _ _ R) i j = 0)
    (h2 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → ((P⁻¹ : GL _ R) : Matrix _ _ R) i j = 0) :
    ∃ (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R), P = unip x * lev R r s m := by
  set e := GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) with he
  set Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := (P : Matrix _ _ R).submatrix e e with hQd
  set Q' : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := ((P⁻¹ : GL _ R) : Matrix _ _ R).submatrix e e with hQ'd
  have hQQ : Q * Q' = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hQQ' : Q' * Q = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hz : Q.toBlocks₂₁ = 0 := by
    ext i j
    exact h1 _ _ (by simp [he]) (by simp [he])
  have hz' : Q'.toBlocks₂₁ = 0 := by
    ext i j
    exact h2 _ _ (by simp [he]) (by simp [he])
  have hb : Q = fromBlocks Q.toBlocks₁₁ Q.toBlocks₁₂ 0 Q.toBlocks₂₂ := by
    rw [← hz, fromBlocks_toBlocks]
  have hb' : Q' = fromBlocks Q'.toBlocks₁₁ Q'.toBlocks₁₂ 0 Q'.toBlocks₂₂ := by
    rw [← hz', fromBlocks_toBlocks]
  generalize Q.toBlocks₁₁ = A at hb
  generalize Q.toBlocks₁₂ = B at hb
  generalize Q.toBlocks₂₂ = D at hb
  generalize Q'.toBlocks₁₁ = A' at hb'
  generalize Q'.toBlocks₁₂ = B' at hb'
  generalize Q'.toBlocks₂₂ = D' at hb'
  rw [hb, hb', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hQQ hQQ'
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ'
  obtain ⟨a1, -, -, d1⟩ := hQQ
  obtain ⟨a2, -, -, d2⟩ := hQQ'
  let X : Matrix (Fin r) (Fin s) R := B * D'
  let x : BlockIx (r + s) r → R := fun p =>
    X ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩
  let m : GL (Fin r) R × GL (Fin s) R := (⟨A, A', a1, a2⟩, ⟨D, D', d1, d2⟩)
  refine ⟨x, m, Units.ext ?_⟩
  have hn : (nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e = fromBlocks 0 X 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [nilM, he]
    · have h : (((e (Sum.inl i) : Fin (r + s)) : ℕ) < r ∧ r ≤ ((e (Sum.inr j) : Fin (r + s)) : ℕ)) := by
        simp [he]
      simp only [submatrix_apply, nilM, of_apply, dif_pos h, fromBlocks_apply₁₂, x]
      congr 1
      exact Fin.ext (by simp [he])
    · simp [nilM, he]
    · simp [nilM, he]
  have hu : ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks 1 X 0 1 := by
    change (1 + nilM x : Matrix _ _ R).submatrix e e = _
    have h : (1 + nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e =
        (1 : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e + (nilM x).submatrix e e := rfl
    rw [h, Matrix.submatrix_one_equiv, hn, ← fromBlocks_one, fromBlocks_add]
    simp
  have hl : ((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks A 0 0 D := by
    rw [lev, GlobalTheory.SmGL.val_emb₂]
    ext i j
    simp [m, ← he]
  have hinj : ∀ M N : Matrix (Fin (r + s)) (Fin (r + s)) R, M.submatrix e e = N.submatrix e e → M = N := by
    intro M N h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa using this
  apply hinj
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ e, hu, hl, fromBlocks_multiply, ← hQd, hb]
  simp [X, Matrix.mul_assoc, d2]

theorem exists_unip_lev_integral (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ)
    (k : GL (Fin (r + s)) (Af E)) :
    ∃ (x : BlockIx (r + s) r → Af E) (m : GL (Fin r) (Af E) × GL (Fin s) (Af E)) (c : GL (Fin (r + s)) (Af E)),
      c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (r + s) ∧ k = unip x * lev (Af E) r s m * c := by
  classical
  let φ := GroundTheory.Automorphic.AdelicGLn.finiteRestrictedEquiv E (r + s)
  let β : Fin (r + s) → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hβ : Monotone β := by
    intro i j hij
    have : (i : ℕ) ≤ j := hij
    simp only [β]
    split_ifs <;> omega
  have loc : ∀ v : HeightOneSpectrum (𝓞 E), ∃ p ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β,
      ∃ c ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s),
        (φ k v : GL (Fin (r + s)) (v.adicCompletion E)) = p * c ∧
        (φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) → p = 1) := by
    intro v
    by_cases h : φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s)
    · exact ⟨1, one_mem _, φ k v, h, (one_mul _).symm, fun _ => rfl⟩
    · obtain ⟨p, hp, c, hc, e⟩ := GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL
        (v.adicCompletion E) (r + s) hβ (φ k v)
      exact ⟨p, hp, c, hc, e, fun h' => absurd h' h⟩
  choose p hp c hc hk h1 using loc
  let P' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨p, by
      filter_upwards [(φ k).2] with v hv
      rw [h1 v hv]
      exact one_mem _⟩
  let C' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨c, Filter.Eventually.of_forall hc⟩
  have hs : ∀ y, φ (φ.symm y) = y := fun y => φ.apply_symm_apply y
  have hPC : k = φ.symm P' * φ.symm C' := by
    apply φ.injective
    rw [map_mul, hs, hs]
    ext v : 1
    exact hk v
  have hPv : ∀ v, φ (φ.symm P') v = p v := fun v => by rw [hs]; rfl
  have hzero : ∀ (q : GL (Fin (r + s)) (Af E)),
      (∀ v, φ q v ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (q : Matrix _ _ (Af E)) i j = 0 := by
    intro q hq i j hi hj
    refine FiniteAdeleRing.ext _ fun v => ?_
    have hlt : β j < β i := by simp [β, hj, Nat.not_lt.2 hi]
    exact hq v hlt
  obtain ⟨x, m, hxm⟩ := exists_unip_mul_lev r s (φ.symm P')
    (hzero _ fun v => by rw [hPv]; exact hp v)
    (hzero _ fun v => by
      rw [map_inv, RestrictedProduct.inv_apply, hPv]
      exact inv_mem (hp v))
  refine ⟨x, m, φ.symm C', ?_, by rw [hPC, hxm]⟩
  rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff_forall]
  intro v
  have : φ (φ.symm C') v = c v := by rw [hs]; rfl
  change φ (φ.symm C') v ∈ _
  rw [this]
  exact hc v

end GlobalTheory.CompanionTheory.CTFin.IwaFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocalFieldPow


open ValuativeRel in
theorem exists_unit_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  intro k _ _ _ _
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  have hr : r ≠ 0 := by simpa using hr0
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨Units.mk0 r hr, ?_⟩
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  rw [Units.val_mk0] at hm
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : ValuativeRel.valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ ValuativeRel.valuation k r ^ m := by
    simpa using pow_le_pow_of_le_one zero_le' hr1.le hn
  simpa using lt_of_le_of_lt h hm

end GlobalTheory.CompanionTheory.LocalFieldPow
end

