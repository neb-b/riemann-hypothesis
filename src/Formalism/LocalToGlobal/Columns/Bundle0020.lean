module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0018
public import Formalism.LocalToGlobal.Columns.Bundle0019
public import Formalism.LocalToGlobal.HermitianForms.Bundle0005
public import Formalism.LocalToGlobal.Columns.WordFin
public import Formalism.LocalToGlobal.Columns.Bundle0015
public import Formalism.LocalToGlobal.Columns.Bundle0009

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.BrpAevalScaleMonomial
section
open MvPolynomial NumberField
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section Scale

variable {K σ : Type} [Field K] [Fintype σ]

theorem brp_aeval_scale_monomial (m : σ →₀ ℕ) (c t : K) :
    aeval (fun v => C t * X v) (monomial m c) = t ^ (m.sum fun _ e => e) • monomial m c := by
  rw [aeval_monomial, monomial_eq, smul_eq_C_mul, algebraMap_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have h : (m.prod fun _ e => (C t : MvPolynomial σ K) ^ e) = C (t ^ (m.sum fun _ e => e)) := by
    simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum, map_pow]
  rw [h, map_pow]
  ring

theorem brp_aeval_scale_whom {r n : ℕ} (ν : Fin n → ℕ) (Q : MvPolynomial (Fin r × Fin n) K)
    (hQ : Q ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) (t : K) :
    aeval (fun v => C t * X v) Q = t ^ (∑ s, ν s) • Q := by
  have hQ' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) Q ν := by
    simpa [mem_weightedHomogeneousSubmodule] using hQ
  have hdeg : ∀ m ∈ Q.support, (m.sum fun _ e => e) = ∑ s, ν s := by
    intro m hm
    rw [← hQ' (mem_support_iff.mp hm)]
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply]
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [brp_aeval_scale_monomial, hdeg m hm]

end Scale

section Scalar

variable (K : Type) [Field K] {n : ℕ}

def brpSc (t : Kˣ) : GL (Fin n) K := Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom t

theorem brpSc_coe (t : Kˣ) : ((brpSc K t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (t : K) • 1 := by
  show algebraMap K (Matrix (Fin n) (Fin n) K) (t : K) = _
  exact Algebra.algebraMap_eq_smul_one _

theorem brp_natW_cast (lam : DomWeight n) (i : Fin n) : ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hn : 0 < n := Fin.pos i
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dite_eq_left hn]
    exact lam.anti (show i ≤ ⟨n - 1, by omega⟩ from Fin.le_iff_val_le_val.mpr (by simp; omega))
  simp only [DomWeight.natW]
  exact Int.toNat_of_nonneg (by omega)

theorem brp_wsum (lam : DomWeight n) :
    (∑ i, lam.w i) = ((∑ i, lam.natW i : ℕ) : ℤ) + n * lam.detShift := by
  push_cast
  simp only [brp_natW_cast, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

end Scalar

section Chi

variable (K : Type) [Field K] {n : ℕ}

def wsum (lam : DomWeight n) : ℤ := ∑ i, lam.w i

end Chi

section ChiPow

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

def brpGL (M : Matrix (Fin n) (Fin n) K) (h : IsUnit M.det) : GL (Fin n) K := Matrix.nonsingInvUnit M h

theorem brpGL_coe (M : Matrix (Fin n) (Fin n) K) (h : IsUnit M.det) : ((brpGL K M h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := rfl

theorem brp_isUnit_transvection (i j : Fin n) (hij : i ≠ j) (c : K) : IsUnit (Matrix.transvection i j c).det := by
  rw [Matrix.det_transvection_of_ne _ _ hij]
  exact isUnit_one

theorem brp_diag_transvection (i j : Fin n) (hij : i ≠ j) (c : K) :
    Matrix.diagonal (Function.update (1 : Fin n → K) i 2) * Matrix.transvection i j c =
      Matrix.transvection i j (2 * c) * Matrix.diagonal (Function.update (1 : Fin n → K) i 2) := by
  have h1 : Matrix.diagonal (Function.update (1 : Fin n → K) i 2) * Matrix.single i j c =
      Matrix.single i j (2 * c) := by
    ext a b
    rw [Matrix.diagonal_mul]
    by_cases ha : a = i
    · subst ha
      by_cases hb : j = b <;> simp [Matrix.single_apply, hb]
    · simp [Matrix.single_apply, ha, Ne.symm ha]
  have h2 : Matrix.single i j (2 * c) * Matrix.diagonal (Function.update (1 : Fin n → K) i 2) =
      Matrix.single i j (2 * c) := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b = j
    · subst hb
      simp [Function.update_apply, Ne.symm hij]
    · simp [Matrix.single_apply, Ne.symm hb]
  rw [Matrix.transvection, Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]

def brpDiag : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom).comp (MulEquiv.piUnits.symm.toMonoidHom)

theorem brpDiag_coe (d : Fin n → Kˣ) :
    ((brpDiag K d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun a => (d a : K) := by rfl

end ChiPow

section ChiPow2

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

theorem brp_isUnit_perm (σ : Equiv.Perm (Fin n)) : IsUnit (Equiv.Perm.permMatrix K σ).det := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem brp_perm_diag (σ : Equiv.Perm (Fin n)) (f : Fin n → K) :
    Equiv.Perm.permMatrix K σ * Matrix.diagonal f = Matrix.diagonal (f ∘ σ) * Equiv.Perm.permMatrix K σ := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
  by_cases h : σ a = b
  · subst h
    exact mul_comm _ _
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]

end ChiPow2

section ChiPow3

variable (K : Type) [Field K] [CharZero K] {n : ℕ}

theorem brpDiag_const (t : Kˣ) : brpDiag K (n := n) (fun _ => t) = brpSc K t := by
  apply Units.ext
  rw [brpDiag_coe, brpSc_coe, Matrix.smul_one_eq_diagonal]

theorem brp_coe_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    (((L.map fun t => brpGL K t.toMatrix (by rw [t.det]; exact isUnit_one)).prod : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, Units.val_mul, ih, brpGL_coe, List.map_cons, List.prod_cons]

theorem brp_det_list_transvec (L : List (Matrix.TransvectionStruct (Fin n) K)) :
    (L.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, t.det, one_mul]

end ChiPow3

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LastVectorMemSpan
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

variable (T : CF.TilTied u A K (P D.R.m le_rfl))




end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCrd
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SpStd (B : ColBase) : Prop where
  X_on : ∀ i, i ≤ B.R.m → ∀ a b, (B.sp.X i).hT ((B.sp.X i).frame a) ((B.sp.X i).frame b) = if a = b then 1 else 0
  selfDual_span_frame_X : ∀ i, i ≤ B.R.m → (B.sp.X i).L0 = Submodule.span (𝓞 B.host.E) (Set.range (B.sp.X i).frame)
  P_on : ∀ a b, B.sp.X'.hT (B.sp.X'.frame a) (B.sp.X'.frame b) = if a = b then 1 else 0
  selfDual_span_frame_auxiliary : B.sp.X'.L0 = Submodule.span (𝓞 B.host.E) (Set.range B.sp.X'.frame)
  iX' : ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b →
    B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b
  z : ∃ c : B.host.E, ∀ b : Fin (B.sp.X B.R.m).rank, (b : ℕ) + 1 = (B.sp.X B.R.m).rank → B.sp.z = c • (B.sp.X B.R.m).frame b

structure HostHyp (d : ColDat) : Prop where
  embE_φ₀ : d.what₂.embLL.comp d.embE = d.host.φ₀
  piT_K : ∀ u, (d.piT u : d.host.E) ∈ d.host.K
  piG_K : ∀ i, (d.piG i : d.host.E) ∈ d.host.K
  cond_eq : d.cond = d.host.QS * d.host.q * d.host.d
  val_eq : ∀ w (x : d.what₂.LL), x ≠ 0 → d.what₂.places.val w x = ((vAdd (d.plEq w) x : ℤ) : WithTop ℤ)

variable {d : ColDat} (a : ColArgs d)

theorem gramN_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : CF.gramN (d.colRec a) i hi = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame _) ((d.sp.X i).frame _) = _
  rw [hS.X_on i hi, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem gramP_eq (hS : SpStd d.toColBase) : CF.gramP (d.colRec a) = 1 := by
  refine Matrix.ext fun x y => ?_
  show d.sp.X'.hT (d.sp.X'.frame _) (d.sp.X'.frame _) = _
  rw [hS.P_on, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

private theorem map_clsLat_crd (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
    (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    (d.clsLat u i c).map ((d.crd i hi).toLinearMap.restrictScalars (𝓞 d.host.E)) = (d.repr u i c).1.L := by
  unfold ColDat.clsLat
  rw [dite_eq_left hi, ← Submodule.map_comp, ← LinearMap.restrictScalars_comp,
    LinearEquiv.comp_symm, LinearMap.restrictScalars_id, Submodule.map_id]

theorem clsCrd_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    CF.clsCrd (d.colRec a) u i hi c = (d.repr u i c).1.L :=
  map_clsLat_crd u i hi c

theorem embT_eq (hH : HostHyp d) : CF.embT (d.colRec a) = d.X.embC d.σ₀ := by
  funext τ
  show d.host.φ₀.comp _ = (d.what₂.embLL).comp (d.embE.comp _)
  rw [← hH.embE_φ₀, RingHom.comp_assoc]

theorem T_eq (u : d.what₂.Word) : ((d.colRec a).mem u).A.T = d.T u := rfl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlPl
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E)
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))

theorem glk_val_lt (x : v.adicCompletionIntegers F) (h : IsLocalRing.residue (v.adicCompletionIntegers F) x = 0) :
    Valued.v (x : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 x.2
  refine lt_of_le_of_ne hle fun h1 => h ?_
  have hx0 : (x : v.adicCompletion F) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  let y : v.adicCompletionIntegers F := ⟨(x : v.adicCompletion F)⁻¹,
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by rw [map_inv₀, h1, inv_one])⟩
  have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
  exact ⟨⟨x, y, hxy, (mul_comm _ _).trans hxy⟩, rfl⟩

theorem gloRho_oToS (a : 𝓞 E) : gloRho v spl halg (oToS F E a) = IsLocalRing.residue (v.adicCompletionIntegers F)
    ⟨gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a)), by
      have := gloPhi_int v spl halg _ (afsplit_prV_int v _ (oToS F E a).2)
      rwa [show ((oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) from rfl, afsplit_prV_inclE] at this⟩ := by
  rw [gloRho_apply]
  congr 1


include hc in
theorem glk_ker (w : Pl E) (hov : IsOver v w) (ϖ : 𝓞 E) (h2 : cO E ϖ ∉ w.asIdeal)
    (hval : Valued.v (gloPhi v spl (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (by rw [map_zero]; exact zero_mem _)
  have hϖ : gloRho v spl halg (oToS F E ϖ) = 0 := by
    rw [gloRho_oToS]
    exact glo_res_zero v _ hval
  let Q : Pl E :=
    { asIdeal := RingHom.ker ((gloRho v spl halg).comp (oToS F E))
      isPrime := RingHom.ker_isPrime _
      ne_bot := fun hb => hϖ0 (by
        have : ϖ ∈ RingHom.ker ((gloRho v spl halg).comp (oToS F E)) := hϖ
        rwa [hb, Ideal.mem_bot] at this) }
  have hQ : IsOver v Q := by
    show v.asIdeal = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    ext r
    rw [Ideal.mem_comap]
    show r ∈ v.asIdeal ↔ gloRho v spl halg (oToS F E (algebraMap (𝓞 F) (𝓞 E) r)) = 0
    rw [gloRho_algMap]
    constructor
    · intro hr
      refine glo_res_zero v _ ?_
      show Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1
      rw [csApprox_val_int]
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
    · intro hr
      have := glk_val_lt v _ hr
      change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 at this
      rw [csApprox_val_int] at this
      exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).1 this
  rcases rll_over_cases hc hov hQ with h | h
  · intro a ha
    have : a ∈ Q.asIdeal := by rw [h]; exact ha
    exact this
  · exfalso
    have : ϖ ∈ Q.asIdeal := hϖ
    rw [h, mem_conjP] at this
    exact h2 this

end Ker

section Pl

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

structure GSplit where
  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
    X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F
  sp_sig : ∀ i v h x, sp i v h (sigR hc.sig (v.adicCompletion X.F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion X.F), sp i v h ((1 : X.E) ⊗ₜ[X.F] a) = (a, a)
  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := X.F) (v.adicCompletion X.F) (hc.sig (Pr.piG i : X.E)))).1 < 1


variable {hc}



end Pl

end Formalism.L2.Col
end
end

