module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Norm

section Abstract

variable {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
  (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A)

theorem row_span {Z : Matrix (Fin r) (Fin n) A} {I : Set (Fin r)} {a : Fin r} (hz : ∀ i ∈ I, (Z * X) a i = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : (Z *ᵥ y) a = 0 := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.ker (LinearMap.proj a ∘ₗ Z.mulVecLin) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact hz i hi
  exact this hy

theorem blk_mulVec (y : Fin n → A) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y =
      y + X.submatrix id e *ᵥ (P *ᵥ fun a => (K *ᵥ y) (e a)) + Y.submatrix id e *ᵥ (Q *ᵥ fun a => (L *ᵥ y) (e a)) := by
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rfl

theorem blk_span (hLX : L * X = 0) (hKX : K * X = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i _ => by rw [hLX]; rfl) hy
  rw [blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero]
  refine add_mem hy ?_
  rcases hI with hI | hI
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a, rfl⟩)
  · have h2 : (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hI a hi) hy
    rw [h2, mulVec_zero, mulVec_zero]
    exact zero_mem _

theorem blk_perp (hLX : L * X = 0) (hLY : L * Y = 1) {I : Set (Fin r)} (hI : (∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I)
    {y : Fin n → A} (hy : ∀ i ∈ I, (L *ᵥ y) i = 0) : ∀ i ∈ I,
    (L *ᵥ ((1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y)) i = 0 := by
  intro i hi
  have h1 : L * X.submatrix id e = 0 := by
    ext a b
    exact congrFun (congrFun hLX a) (e b)
  rw [blk_mulVec, mulVec_add, mulVec_add, mulVec_mulVec _ L (X.submatrix id e), h1, zero_mulVec, add_zero,
    Pi.add_apply, hy i hi, zero_add]
  rcases hI with hI | hI
  · have h2 : (fun a => (L *ᵥ y) (e a)) = 0 := funext fun a => hy _ (hI a)
    rw [h2, mulVec_zero, mulVec_zero, mulVec_zero]
    rfl
  · rw [mulVec_mulVec _ L]
    change ∑ a, (L * Y.submatrix id e) i a * _ = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    have : (L * Y.submatrix id e) i a = 0 := by
      change (L * Y) i (e a) = 0
      rw [hLY, Matrix.one_apply_ne]
      rintro rfl
      exact hI a hi
    rw [this, zero_mul]

end Abstract

open GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}


omit [NumberField E] in
theorem conj_mem_trivOn {A B B' : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {m u : GAd σ J}
    (h1 : ∀ y ∈ A, (matHom _ σ J m).1 *ᵥ y ∈ A) (h2 : ∀ y ∈ A, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A)
    (h3 : ∀ y ∈ B, (matHom _ σ J m⁻¹).1 *ᵥ y ∈ B') (hu : u ∈ trivOn σ J A B') : m * u * m⁻¹ ∈ trivOn σ J A B := by
  have e : ∀ (a : GAd σ J) y, (matHom _ σ J a⁻¹).1 *ᵥ (matHom _ σ J a).1 *ᵥ y = y := fun a y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have e' : ∀ y, (matHom _ σ J m).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y = y := fun y => by
    simpa only [inv_inv] using e m⁻¹ y
  have i1 : ∀ y, y ∈ A ↔ (matHom _ σ J m).1 *ᵥ y ∈ A := fun y => ⟨h1 y, fun h => e m y ▸ h2 _ h⟩
  have i2 : ∀ y, y ∈ A ↔ (matHom _ σ J m⁻¹).1 *ᵥ y ∈ A := fun y => ⟨h2 y, fun h => e' y ▸ h1 _ h⟩
  have v : ∀ y, (matHom _ σ J (m * u * m⁻¹)).1 *ᵥ y =
      (matHom _ σ J m).1 *ᵥ (matHom _ σ J u).1 *ᵥ (matHom _ σ J m⁻¹).1 *ᵥ y := fun y => by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mulVec_mulVec, mulVec_mulVec]
  refine ⟨fun y => by rw [v, ← i1, ← hu.1, ← i2], fun y hy => ?_⟩
  have := h1 _ (hu.2 _ (h3 y hy))
  rwa [mulVec_sub, e', ← v] at this


omit [NumberField E] in
theorem mem_trivOn_span {A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {u : GAd σ J} {T : Set (Fin r)} {j : Fin r}
    (hj : j ∈ T) (hu : ∀ i ∈ T, u ∈ trivOn σ J A (colSpan F X {i})) : u ∈ trivOn σ J A (colSpan F X T) := by
  refine ⟨(hu j hj).1, fun y hy => ?_⟩
  have : colSpan F X T ≤ A.comap ((matHom _ σ J u).1.mulVecLin - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact (hu i hi).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
  exact this hy

theorem blockEmb_normalises : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      (∀ g, ∀ u ∈ GlobalTheory.StdPar.unip σ J Xf S, ι g * u * (ι g)⁻¹ ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
      ∀ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E), ι (GlobalTheory.CuspRep.infGL E d y) ∈ infPts σ J := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS _ _
  constructor
  · let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
    have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
        adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
    have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
      rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
    have hLY : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
      rw [hm, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have sp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colSpan F X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colSpan F X I := fun g I hI y hy => by
      rw [hι]
      exact blk_span (Y := adMat F Y) e _ _ hLX hKX hI hy
    have pp : ∀ g {I : Set (Fin r)}, ((∀ a, e a ∈ I) ∨ ∀ a, e a ∉ I) → ∀ y ∈ colPerp σ J X I,
        (matHom _ σ J (ι g)).1 *ᵥ y ∈ colPerp σ J X I := fun g I hI y hy => by
      rw [hι]
      simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      exact blk_perp (X := adMat F X) (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ hLX hLY hI hy
    have cp : ∀ p : Fin r → Prop, (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k ∧ p k} := fun p => by
      by_contra hc
      obtain ⟨h1, h2⟩ := not_or.1 hc
      obtain ⟨b, k, hk, hb, hp⟩ : ∃ b, e b ∈ {i | ∃ k ∈ S, i ≤ k ∧ p k} := by simpa only [not_forall, not_not] using h2
      refine h1 fun a => ⟨k, hk, ?_, hp⟩
      have hb' : l + b.val ≤ k.val := hb
      have : ¬ k.val + 1 < l + d := fun h' => hS k (by omega) h' hk
      change l + a.val ≤ k.val
      omega
    have cp' : (∀ a, e a ∈ {i | ∃ k ∈ S, i ≤ k}) ∨ ∀ a, e a ∉ {i | ∃ k ∈ S, i ≤ k} := by
      simpa only [and_true] using cp fun _ => True
    intro g u hu
    refine ⟨Subgroup.mem_iInf.2 fun j => ?_, conj_mem_trivOn (sp g cp') (map_inv ι g ▸ sp g⁻¹ cp')
      (map_inv ι g ▸ pp g⁻¹ cp') hu.2⟩
    have hu1 := Subgroup.mem_iInf.1 hu.1
    by_cases hj : j ∈ Set.range e
    · refine conj_mem_trivOn (B' := colSpan F X (Set.range e)) (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (fun y hy => map_inv ι g ▸ sp g⁻¹ (I := Set.range e) (Or.inl fun a => Set.mem_range_self a) y
          (Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj)) hy)) (mem_trivOn_span hj ?_)
      obtain ⟨b, rfl⟩ := hj
      rintro _ ⟨a, rfl⟩
      have key : ∀ a b : Fin d, ∀ k ∈ S, k < e a → k < e b := fun a b k hk hka => by
        have h1 : k.val < l + a.val := hka
        have h2 : ¬ l ≤ k.val := fun h' => hS k h' (by omega) hk
        change k.val < l + b.val
        omega
      have : {i | ∃ k ∈ S, i ≤ k ∧ k < e b} = {i | ∃ k ∈ S, i ≤ k ∧ k < e a} := Set.ext fun i =>
        ⟨fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩, fun ⟨k, hk, h1, h2⟩ => ⟨k, hk, h1, key _ _ k hk h2⟩⟩
      rw [this]
      exact hu1 _
    · exact conj_mem_trivOn (sp g (cp _)) (map_inv ι g ▸ sp g⁻¹ (cp _))
        (map_inv ι g ▸ sp g⁻¹ (I := {j}) (Or.inr fun a (ha : e a = j) => hj (Exists.intro a ha))) (hu1 j)
  · have k1 : ∀ z, GlobalTheory.LFun.finTens F E (Φ.symm z) = (GlobalTheory.LFun.finAdEquiv F E).symm (GlobalTheory.CuspRep.pFin E z) := fun z => by
      have := congrArg (GlobalTheory.CuspRep.pFin E) (hΦ (Φ.symm z))
      rw [RingEquiv.apply_symm_apply] at this
      rw [this]
      exact ((GlobalTheory.LFun.finAdEquiv F E).symm_apply_apply _).symm
    have k2 : ∀ y, ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) = 1 := fun y => by
      have := congrArg Units.val (GlobalTheory.CuspRep.pFin_infGL (E := E) y)
      have e : ((GlobalTheory.CuspRep.infGL E d y).1.map Φ.symm).map (GlobalTheory.LFun.finTens F E) =
          ((GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E)).map (GlobalTheory.LFun.finAdEquiv F E).symm :=
        Matrix.ext fun a b => k1 _
      rw [e, show (GlobalTheory.CuspRep.infGL E d y).1.map (GlobalTheory.CuspRep.pFin E) = 1 from this]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have k3 : ∀ x, sigR (Af F) σ (GlobalTheory.LFun.finTens F E x) = GlobalTheory.LFun.finTens F E (sigR (AF F) σ x) := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => rfl
    intro y
    refine Units.ext ?_
    change (matHom _ σ J (ι (GlobalTheory.CuspRep.infGL E d y))).1.map (GlobalTheory.LFun.finTens F E) = 1
    have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)).map (GlobalTheory.LFun.finTens F E) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [hι, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), k2,
      ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ (sigR (Af F) σ) _ k3, ← map_inv, k2, o, o, Formalism.UG.cT_one, sub_self]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

end GlobalTheory.BlockForms.Norm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.LeviHC

section Alg

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def FinMod (K : Submodule ℂ M) (A : Subalgebra ℂ (Module.End ℂ M)) (v : M) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ A, y = K.mkQ (a v)})

def MonicFactorFinite : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (p q : ℂ → Module.End ℂ N),
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    ∀ v : N, FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range fun u => p u * q u), y = a v}) →
      FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range p), y = a v})

def MonicFactorFiniteMod : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K ∧ q u x ∈ K) →
    (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
    ∀ v ∈ M', FinMod K (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v

theorem coeff_mem_span {d : ℕ} {a : ℕ → M} {p : ℂ → M} (hp : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i)
    {i : ℕ} (hi : i < d + 1) : a i ∈ Submodule.span ℂ (Set.range p) := by
  set W := Submodule.span ℂ (Set.range p)
  have hdual : ∀ f : Module.Dual ℂ (M ⧸ W), f (W.mkQ (a i)) = 0 := by
    intro f
    let P : Polynomial ℂ :=
      ∑ j ∈ Finset.range (d + 1), Polynomial.C (f (W.mkQ (a j))) * Polynomial.X ^ j
    have hP : P = 0 := by
      apply Polynomial.funext
      intro u
      have h0 : W.mkQ (p u) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span ⟨u, rfl⟩)
      have h1 : f (W.mkQ (p u)) = ∑ j ∈ Finset.range (d + 1), u ^ j * f (W.mkQ (a j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hp u, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, smul_eq_mul]
      rw [h0, map_zero] at h1
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff i) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_ite_eq] at hc
    simpa [Finset.mem_range.2 hi] using hc
  have hq : W.mkQ (a i) = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ _).1 hdual
  exact (Submodule.Quotient.mk_eq_zero W).1 hq

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}



variable (σ J) in
def IsLineOf {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z)


variable {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}

theorem IsLineOf.skew (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 := by
  apply GlobalTheory.LineDerSum.skew_of_exp_unitary
  intro t
  obtain ⟨y, -, hy⟩ := hγ t
  rw [← hy, GlobalTheory.Orb.archMat_eq_archEquiv J h τ y]
  exact (archEquiv J h τ y).2

theorem IsLineOf.isRealLine (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, hγ.skew h, hγ⟩

private theorem conjTranspose_map_eq_of_isHermND (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← h.2.2.2 τ, hJ.1 i j]

private theorem isUnit_det_map_of_det_ne_zero {K : Type} [Field K] {m : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (hM : M.det ≠ 0) (τ : K →+* ℂ) : IsUnit (M.map τ).det := by
  have hd : (M.map τ).det = τ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 hM

theorem conjTranspose_map (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := conjTranspose_map_eq_of_isHermND h hJ τ

omit [NumberField F] [NumberField E] in
theorem isUnit_det_map (hJ : IsHermND σ J) (τ : E →+* ℂ) : IsUnit (J.map τ).det := isUnit_det_map_of_det_ne_zero hJ.2 τ

variable {n₁ : ℕ}




end GlobalTheory.LeviHC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRank
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv.Recentre

variable {k : Type} [Field k] [ValuativeRel k]

theorem vecMul_bound {r : ℕ} (E : Matrix (Fin r) (Fin r) k) (δ b : ValueGroupWithZero k)
    (hδ : δ < 1) (hE : ∀ l l', valuation k (E l l') ≤ δ) (s w : Fin r → k)
    (hw : ∀ l, valuation k (w l) ≤ b) (hs : s ᵥ* (1 + E) = w) : ∀ l, valuation k (s l) ≤ b := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · intro l; exact isEmptyElim l
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty
  have key : s l₀ = w l₀ - ∑ l, s l * E l l₀ := by
    have := congrFun hs l₀
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this
    rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ := by
    apply Valuation.map_sum_le
    intro l _
    rw [map_mul]
    exact mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)
  have hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ) := by
    calc valuation k (s l₀) = valuation k (w l₀ - ∑ l, s l * E l l₀) := by rw [← key]
      _ ≤ max (valuation k (w l₀)) (valuation k (∑ l, s l * E l l₀)) := Valuation.map_sub _ _ _
      _ ≤ max b (valuation k (s l₀) * δ) := max_le_max (hw l₀) hsum
  have hμb : valuation k (s l₀) ≤ b := by
    rcases le_max_iff.1 hμ with h | h
    · exact h
    · by_cases h0 : valuation k (s l₀) = 0
      · rw [h0]; exact zero_le'
      · exfalso
        have h2 := mul_le_mul_left h (valuation k (s l₀))⁻¹
        rw [mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
        exact absurd hδ (not_lt.2 h2)
  exact fun l => (hl₀ l (Finset.mem_univ _)).trans hμb

end GlobalTheory.RankCoinv.Recentre

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀
  classical
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hv0 : valuation k (ϖ : k) ≠ 0 := by simp
  have vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n := by intro n; simp
  have vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹ := by simp
  by_cases hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r
  swap
  · apply Submodule.mem_sup_left
    refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩
    unfold GlobalTheory.RankCoinv.boxFn
    apply Set.indicator_of_notMem
    intro hYb; exact hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩
  obtain ⟨X₂, hX₂, hrk⟩ := hex
  set u := valuation k (ϖ : k) with hu
  have hQ' : ∀ j l, valuation k (Q j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)
  have hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m := fun i j => by
    rw [Matrix.sub_apply, ← vpow]; exact hX₂ i j
  have hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹ := fun l i => (hH l i).trans_eq vinv
  have hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m := fun l j => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro i _; rw [map_mul]
    exact mul_le_mul' (hHb l i) (hD i j)
  have hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m := fun l l' => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ (u ^ c)⁻¹ * u ^ m * 1 := mul_le_mul' (hHD l j) (hQ' j l')
      _ = _ := mul_one _
  have hm1 : u ^ m ≤ u ^ (c + 1) := pow_le_pow_right_of_le_one' hlt.le hcm
  have hδ : (u ^ c)⁻¹ * u ^ m < 1 := by
    calc (u ^ c)⁻¹ * u ^ m ≤ (u ^ c)⁻¹ * u ^ (c + 1) := mul_le_mul' le_rfl hm1
      _ = u := by rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ < 1 := hlt
  have hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hHCQ]; abel
  have hunit : IsUnit (H * X₂ * Q) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro a a' haa
    have h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0 := by
      rw [← hM, Matrix.sub_vecMul]; exact sub_eq_zero.2 haa
    funext l
    have h1 := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l
    have h2 : (a - a') l = 0 := (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    exact sub_eq_zero.1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀
  have hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← hs]
  have hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1) := fun j => by
    have h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1) := ((hX₂ i₀ j).trans_eq (vpow m)).trans hm1
    have h2 : valuation k (C i₀ j) ≤ u ^ (c + 1) := (hCi₀ j).trans_eq (vpow _)
    calc valuation k (X₂ i₀ j) = valuation k ((X₂ i₀ j - C i₀ j) + C i₀ j) := by rw [sub_add_cancel]
      _ ≤ _ := Valuation.map_add_le _ h1 h2
  have hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1) := fun l => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * 1 := mul_le_mul' (hX₂i₀ j) (hQ' j l)
      _ = _ := mul_one _
  have hsb := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw
  have hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m := fun j => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro l _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * ((u ^ c)⁻¹ * u ^ m) := mul_le_mul' (hsb l) (hHD l j)
      _ = u * u ^ m := by
        rw [pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _
      _ = u ^ m := one_mul _
  set C' := Matrix.updateRow C i₀ 0 with hC'
  have hHC' : H * C' = H * C := by
    ext l j
    simp only [Matrix.mul_apply, C', Matrix.updateRow_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · subst h; simp [hHi₀]
    · rfl
  have hcore := _root_.GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm
    (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])
  have hstep := _root_.GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan k A D ϖ ν β i₀ r c m C' H s hHi₀ hH
    (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))
  have e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C)) := by
    rw [Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]
  have hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) =
      Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C))) := by
    rw [hHC', e1]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]
  have hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m) := by
    rw [hC'']
    intro i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self]
      calc valuation k ((X₂ i - s ᵥ* (H * (X₂ - C))) j - C i j)
          = valuation k ((X₂ i j - C i j) - (s ᵥ* (H * (X₂ - C))) j) := by
            congr 1; rw [Pi.sub_apply]; ring
        _ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) :=
            Valuation.map_sub _ _ _
        _ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)
        _ = _ := (vpow m).symm
    · rw [Matrix.updateRow_ne hi]; simp
  rw [GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem] at hstep
  rw [← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore
end

