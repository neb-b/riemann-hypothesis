module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNA
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def SD (Λ : Submodule (𝓞 E) S.V) : Prop := ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x)

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap S x y

theorem hT_smulL (a : E) (x v : S.V) : S.hT (a • x) v = star a * S.hT x v := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem oSmul (o : 𝓞 E) (x : S.V) : o • x = (o : E) • x := (algebraMap_smul E o x).symm

theorem coe_ne_zero {d : 𝓞 E} (hd : d ≠ 0) : (d : E) ≠ 0 := by
  intro h; apply hd; exact RingOfIntegers.coe_eq_zero_iff.1 h

theorem isInt_star {a : E} (h : IsIntegral ℤ a) : IsIntegral ℤ (star a) := by
  have h2 := h.map ((starRingEnd E : E →+* E).toIntAlgHom)
  exact h2

theorem intO {a : E} (h : IsIntegral ℤ a) : ∃ o : 𝓞 E, (o : E) = a := ⟨⟨a, h⟩, rfl⟩

variable {S}

theorem int_smul_mem {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : IsIntegral ℤ c) {x : S.V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := intO hc
  rw [← oSmul]
  exact Λ.smul_mem o hx

theorem sd_int {Λ : Submodule (𝓞 E) S.V} (h : SD S Λ) {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    IsIntegral ℤ (S.hT y x) := (h x).1 hx y hy

variable (S)

theorem riesz (F : S.V →ₗ[E] E) : ∃ w, ∀ v, S.hT w v = F v := by
  classical
  let b := S.frame
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg b
  refine ⟨∑ j, star (F (b j)) • bs j, fun v => ?_⟩
  have key : S.hT (∑ j, star (F (b j)) • bs j) = F := by
    apply b.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hsw S (b i) (bs i), hbs i i]; simp
    · intro j _ hj
      rw [hsw S (b i) (bs j), hbs i j, if_neg (Ne.symm hj)]; simp
    · simp
  rw [key]

theorem mem_of_orth_orth (X : Submodule E S.V) {w : S.V} (hw : ∀ u ∈ orth S X, S.hT w u = 0) : w ∈ X := by
  have hle : X ≤ orth S (orth S X) := fun x hx => (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => by
    rw [hsw S x u, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hu x hx, star_zero]
  have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S X
  have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S X)
  have heq : X = orth S (orth S X) := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [heq]
  exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => by rw [hsw S w u, hw u hu, star_zero]

theorem proj_quot (P : Submodule (𝓞 E) S.V) (hP : P.FG) (Z : Submodule E S.V) :
    Module.Projective (𝓞 E) (P ⧸ (Z.restrictScalars (𝓞 E)).comap P.subtype) := by
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have : Module.Finite (𝓞 E) P := Module.Finite.iff_fg.2 hP
  have htor : Submodule.torsion (𝓞 E) (P ⧸ K) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submonoid.smul_def, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := coe_ne_zero (nonZeroDivisors.coe_ne_zero a)
    have h1 : ((a : 𝓞 E) : E) • (x : S.V) ∈ Z := by
      have := ha
      simp only [hK, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul,
        Submodule.restrictScalars_mem] at this
      rwa [oSmul] at this
    have h2 := Z.smul_mem ((a : 𝓞 E) : E)⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h2
    simpa [hK] using h2
  have : Module.Flat (𝓞 E) (P ⧸ K) := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have : Module.FinitePresentation (𝓞 E) (P ⧸ K) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem glift (P Q : Submodule (𝓞 E) S.V) (hP : P.FG) (Y Z : Submodule E S.V)
    (hPZ : ∀ x ∈ P, x ∈ Z → x ∈ Q) (hs : ∀ x ∈ P, ∃ y ∈ Q, y - x ∈ Y) :
    ∃ δ : P →ₗ[𝓞 E] S.V, (∀ x, δ x ∈ Y) ∧ (∀ x : P, (x : S.V) ∈ Z → δ x = 0) ∧
      (∀ x : P, (x : S.V) + δ x ∈ Q) := by
  classical
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have := proj_quot S P hP Z
  let dif : (P × Q) →ₗ[𝓞 E] S.V := Q.subtype ∘ₗ LinearMap.snd _ _ _ - P.subtype ∘ₗ LinearMap.fst _ _ _
  let R : Submodule (𝓞 E) (P × Q) := (Y.restrictScalars (𝓞 E)).comap dif
  let g : R →ₗ[𝓞 E] (P ⧸ K) := K.mkQ ∘ₗ LinearMap.fst _ _ _ ∘ₗ R.subtype
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    obtain ⟨y, hyQ, hy⟩ := hs x x.2
    refine ⟨⟨(x, ⟨y, hyQ⟩), ?_⟩, rfl⟩
    simpa [R, dif] using hy
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property g LinearMap.id hg
  refine ⟨dif ∘ₗ R.subtype ∘ₗ s ∘ₗ K.mkQ, fun x => ?_, fun x hx => ?_, fun x => ?_⟩
  · exact (s (K.mkQ x)).2
  · have : K.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [hK] using hx
    simp [this]
  · have hgt : g (s (K.mkQ x)) = K.mkQ x := LinearMap.congr_fun hs' (K.mkQ x)
    set t := s (K.mkQ x) with ht
    have h1 : x - (t : P × Q).1 ∈ K := by
      have h0 : K.mkQ (x - (t : P × Q).1) = 0 := by
        have : K.mkQ ((t : P × Q).1) = K.mkQ x := hgt
        rw [map_sub, this, sub_self]
      exact (Submodule.Quotient.mk_eq_zero K).1 h0
    have h2 : ((x : S.V) - ((t : P × Q).1 : S.V)) ∈ Q := by
      refine hPZ _ (P.sub_mem x.2 (t : P × Q).1.2) ?_
      simpa [hK] using h1
    have h3 : (x : S.V) + (dif ∘ₗ R.subtype ∘ₗ s ∘ₗ K.mkQ) x =
        ((t : P × Q).2 : S.V) + ((x : S.V) - ((t : P × Q).1 : S.V)) := by
      simp only [LinearMap.coe_comp, Function.comp_apply, ← ht, dif, LinearMap.sub_apply,
        Submodule.coe_subtype, LinearMap.snd_apply, LinearMap.fst_apply]
      abel
    rw [h3]
    exact Q.add_mem (t : P × Q).2.2 h2

theorem retract (P : Submodule (𝓞 E) S.V) (hP : P.FG) (Z : Submodule E S.V) :
    ∃ π : P →ₗ[𝓞 E] S.V, (∀ x, π x ∈ P ∧ π x ∈ Z) ∧ ∀ x : P, (x : S.V) ∈ Z → π x = x := by
  classical
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have := proj_quot S P hP Z
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property K.mkQ LinearMap.id K.mkQ_surjective
  refine ⟨P.subtype ∘ₗ (LinearMap.id - s ∘ₗ K.mkQ), fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · exact (x - s (K.mkQ x)).2
  · have h1 : x - s (K.mkQ x) ∈ K := by
      have h0 : K.mkQ (x - s (K.mkQ x)) = 0 := by
        have : K.mkQ (s (K.mkQ x)) = K.mkQ x := LinearMap.congr_fun hs' (K.mkQ x)
        rw [map_sub, this, sub_self]
      exact (Submodule.Quotient.mk_eq_zero K).1 h0
    simpa [hK] using h1
  · have : K.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [hK] using hx
    simp [this]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Gram

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

theorem h_sum_smul_left {ι : Type} [Fintype ι] (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  show hL H y (∑ i, c i • v i) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := (hL H y).map_sub x x'

theorem h_sum_smul_right {ι : Type} [Fintype ι] (c : ι → E) (v : ι → V) (w : V) :
    H.h w (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h w (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm (∑ i, c i • v i) w, h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, H.h_herm (v i) w]

theorem isCompl_span_perp {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hG : IsUnit (H.gram v).det) :
    IsCompl (Submodule.span E (Set.range v)) (H.perp (Submodule.span E (Set.range v))) := by
  have hmv : ∀ (c : ι → E) (j : ι), H.h (∑ i, c i • v i) (v j) = (H.gram v *ᵥ c) j := by
    intro c j
    rw [h_sum_smul_left]
    show _ = ∑ i, H.gram v j i * c i
    simp only [HermSp.gram, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have hc : H.gram v *ᵥ c = 0 := by
      funext j
      rw [← hmv]
      exact hxp (v j) (Submodule.subset_span ⟨j, rfl⟩)
    have hc0 : c = 0 := by
      have := congrArg (fun w => (H.gram v)⁻¹ *ᵥ w) hc
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG] using this
    subst hc0
    simp
  · rw [codisjoint_iff, eq_top_iff]
    rintro x -
    set c := (H.gram v)⁻¹ *ᵥ (fun j => H.h x (v j)) with hc
    have hsum : ∑ i, c i • v i ∈ Submodule.span E (Set.range v) :=
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩
    have hperp : x - ∑ i, c i • v i ∈ H.perp (Submodule.span E (Set.range v)) := by
      intro y hy
      obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
      rw [h_sum_smul_right]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [h_sub_left, hmv, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
      simp
    exact Submodule.mem_sup.2 ⟨_, hsum, _, hperp, by abel⟩

variable {r : ℕ}

def cornerM (c : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem cornerM_mul (c : E) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a k : Fin (r + 1)) :
    (cornerM (r := r) c * N) a k = if a = Fin.last r then c * N (Fin.last r) k else 0 := by
  simp only [cornerM, Matrix.mul_apply, Matrix.of_apply]
  split_ifs with ha
  · subst ha
    simp
  · simp [ha]

theorem mul_cornerM (c : E) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (k b : Fin (r + 1)) :
    (N * cornerM (r := r) c) k b = if b = Fin.last r then N k (Fin.last r) * c else 0 := by
  simp only [cornerM, Matrix.mul_apply, Matrix.of_apply]
  split_ifs with hb
  · subst hb
    simp
  · simp [hb]

theorem gram_eq_fromBlocks (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.gram (Sum.elim f f') = fromBlocks (cornerM (-algebraMap F E T)) (H.Zhat f f')
      (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) (cornerM (-algebraMap F E T')) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, cornerM]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hF.2
    · exact hF.1 b a (not_and_or.1 h).symm
  · simp only [HermSp.gram, HermSp.Zhat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂]
  · simp only [HermSp.gram, HermSp.Zhat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁]
    exact H.h_herm (f' a) (f b)
  · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, cornerM]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hF'.2
    · exact hF'.1 b a (not_and_or.1 h).symm

private theorem det_sub_cornerM (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (t : E) :
    (N - cornerM t).det = N.det - t * (N.submatrix Fin.castSucc Fin.castSucc).det := by
  have hP : (-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  have hsub : ∀ j : Fin (r + 1), (N - cornerM t).submatrix (Fin.last r).succAbove j.succAbove =
      N.submatrix (Fin.last r).succAbove j.succAbove := by
    intro j
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, cornerM, Matrix.of_apply, Fin.succAbove_last]
    rw [if_neg (fun h => (Fin.castSucc_lt_last a).ne h.1), sub_zero]
  have hrow : ∀ k : Fin r, (N - cornerM t : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Fin.last r) k.castSucc =
      N (Fin.last r) k.castSucc := by
    intro k
    simp only [Matrix.sub_apply, cornerM, Matrix.of_apply]
    rw [if_neg (fun h => (Fin.castSucc_lt_last k).ne h.2), sub_zero]
  rw [Matrix.det_succ_row (N - cornerM t) (Fin.last r), Matrix.det_succ_row N (Fin.last r),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hsub, hrow, hP]
  simp only [Matrix.sub_apply, cornerM, Matrix.of_apply, eq_self_iff_true, and_self, ite_true,
    Fin.succAbove_last]
  ring

private theorem det_cj_transpose_eq_cj_det {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n E) :
    (Matrix.of fun a b => M.L.cj (N b a)).det = M.L.cj N.det := by
  calc (Matrix.of fun a b => M.L.cj (N b a)).det
      = ((M.L.cj : E →+* E).mapMatrix N).transpose.det := rfl
    _ = ((M.L.cj : E →+* E).mapMatrix N).det := Matrix.det_transpose _
    _ = (M.L.cj : E →+* E) N.det := (RingHom.map_det _ _).symm
    _ = M.L.cj N.det := rfl

theorem gram_det (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) :
    ∃ s : E, s * s = 1 ∧ (H.gram (Sum.elim f f')).det * s = H.Gdet f f' T T' := by
  classical
  have hdB : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    rw [HermSp.Dl, dite_eq_left le_rfl]
    exact congrArg Matrix.det (Matrix.ext fun i j => rfl)
  have hdBr : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
    rw [HermSp.Dl, dite_eq_left (by omega : r ≤ r + 1)]
    exact congrArg Matrix.det (Matrix.ext fun i j => rfl)
  haveI hBinv : Invertible (H.Zhat f f') := Matrix.invertibleOfIsUnitDet _ (hdB ▸ hD)
  have hcorner : cornerM (r := r) (-algebraMap F E T') * ⅟(H.Zhat f f') * cornerM (-algebraMap F E T) =
      cornerM (algebraMap F E T * algebraMap F E T' * (⅟(H.Zhat f f')) (Fin.last r) (Fin.last r)) := by
    ext a b
    rw [mul_cornerM, cornerM_mul]
    simp only [cornerM, Matrix.of_apply]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb] <;> ring
  have hP : (-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  have hinv : (⅟(H.Zhat f f')) (Fin.last r) (Fin.last r) =
      Ring.inverse (H.Zhat f f').det * ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, Matrix.smul_apply,
      Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, smul_eq_mul, hP, one_mul]
  have hC : (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)).det = M.L.cj (H.Zhat f f').det :=
    det_cj_transpose_eq_cj_det _
  have hCs : ((Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det :=
    det_cj_transpose_eq_cj_det _
  have hu : (H.Zhat f f').det * Ring.inverse (H.Zhat f f').det = 1 :=
    Ring.mul_inverse_cancel _ (hdB ▸ hD)
  rw [gram_eq_fromBlocks H f f' T T' hF hF']
  refine ⟨((Equiv.Perm.sign (Equiv.sumComm (Fin (r + 1)) (Fin (r + 1))) : ℤ) : E), ?_, ?_⟩
  · rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  · have h1 := Matrix.det_permute' (Equiv.sumComm (Fin (r + 1)) (Fin (r + 1)))
      (Matrix.fromBlocks (cornerM (-algebraMap F E T)) (H.Zhat f f')
        (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) (cornerM (-algebraMap F E T')))
    have hperm : (Matrix.fromBlocks (cornerM (-algebraMap F E T)) (H.Zhat f f')
        (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) (cornerM (-algebraMap F E T'))).submatrix id
          (Equiv.sumComm (Fin (r + 1)) (Fin (r + 1))) =
        Matrix.fromBlocks (H.Zhat f f') (cornerM (-algebraMap F E T)) (cornerM (-algebraMap F E T'))
          (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) := by
      ext (i | i) (j | j) <;> rfl
    rw [hperm, Matrix.det_fromBlocks₁₁, hcorner, det_sub_cornerM, hinv, hC, hCs] at h1
    simp only [HermSp.Gdet, HermSp.normE]
    rw [hdB, hdBr, (algebraMap F E).map_mul T T']
    linear_combination (-1 : E) * h1 - (algebraMap F E T * algebraMap F E T' *
      (((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det *
        M.L.cj ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det)) * hu

theorem isUnit_Gdet (f f' : Fin (r + 1) → V) (T T' : F) (hG : H.Gdet f f' T T' ≠ 0) :
    IsUnit (H.Gdet f f' T T') := by
  have hfix : M.L.cj (H.Gdet f f' T T') = H.Gdet f f' T T' := by
    simp only [HermSp.Gdet, HermSp.normE, map_sub, map_mul, AlgEquiv.commutes, M.L.cj_cj] <;> ring
  obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
  rw [← ha] at hG ⊢
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  exact (IsUnit.mk0 a ha0).map (algebraMap F E)

theorem isCompl_span_frames_W0 (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsCompl (Submodule.span E (Set.range (Sum.elim f f'))) (H.W0 f f') := by
  have hsp : H.Xp f ⊔ H.Xp f' = Submodule.span E (Set.range (Sum.elim f f')) := by
    simp only [HermSp.Xp, Set.Sum.elim_range, Submodule.span_union]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD
  have hu : IsUnit (H.gram (Sum.elim f f')).det := by
    have h' := hG
    rw [← hdet] at h'
    exact isUnit_of_mul_isUnit_left h'
  have hW : H.W0 f f' = H.perp (Submodule.span E (Set.range (Sum.elim f f'))) := by
    rw [← hsp]
    rfl
  rw [hW]
  exact isCompl_span_perp H _ hu

end Gram

end Formalism.L2.SG.LsDatumA
end
end

