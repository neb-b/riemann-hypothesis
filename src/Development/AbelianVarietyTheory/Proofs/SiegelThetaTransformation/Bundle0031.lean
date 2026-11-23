module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsMoveMarked
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Move

theorem exists_pow_le {E : Type} [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) {d : 𝓞 E} (hd : d ≠ 0) :
    ∃ N : ℕ, ∃ t, IsCoprime (Ideal.span {t}) 𝔪 ∧ ∀ b ∈ 𝔪 ^ N, t * b ∈ Ideal.span {d} := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hd)
  haveI : IsArtinianRing (𝓞 E ⧸ Ideal.span {d}) := isArtinian_of_finite
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := 𝓞 E ⧸ Ideal.span {d}) (M := 𝓞 E ⧸ Ideal.span {d})
    ⟨fun n => OrderDual.toDual ((𝔪 ^ n).map (Ideal.Quotient.mk (Ideal.span {d}))),
      fun a b h => Ideal.map_mono (Ideal.pow_le_pow_right h)⟩
  have h1 : (𝔪 ^ N).map (Ideal.Quotient.mk (Ideal.span {d})) =
      (𝔪 ^ (N + 1)).map (Ideal.Quotient.mk (Ideal.span {d})) := hN (N + 1) (Nat.le_succ N)
  have h2 : 𝔪 ^ N ≤ Ideal.span {d} ⊔ 𝔪 • 𝔪 ^ N := by
    have := (Ideal.le_comap_map (f := Ideal.Quotient.mk (Ideal.span {d})) (I := 𝔪 ^ N))
    rw [h1, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm, pow_succ'] at this
    exact this
  exact ⟨N, Lev.nakayama (IsNoetherian.noetherian _) h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem exists_pow_smul {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (v : Fin r → E) :
    ∃ N : ℕ, ∀ b ∈ 𝔪 ^ N, b • v ∈ Lev.loc 𝔪 (𝔪 • X.Λ) := by
  obtain ⟨k, hk, hx⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨N, t, ht, h⟩ := exists_pow_le 𝔪 (d := m * (k : 𝓞 E)) (mul_ne_zero hm0 (by exact_mod_cast hk))
  refine ⟨N, fun b hb => ⟨t, ht, ?_⟩⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h b hb)
  rw [← mul_smul, ← hc, mul_smul, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul hm hx)


omit [IsCMField E] in
theorem isUnit_cols {𝔪 : Ideal (𝓞 E)} (h1 : 𝔪 ≠ ⊤) {L : Lt E r} (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {u : Fin r → Fin r → E}
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ 𝔪 • L) : IsUnit (Matrix.of u)ᵀ := by
  obtain ⟨s, hs, hN⟩ := Lev.nakayama hfg h
  have hs0 : (s : E) ≠ 0 := by simpa using Lev.cop_ne_zero h1 hs
  have hli : LinearIndependent E u := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← hsp, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  exact Matrix.linearIndependent_cols_iff_isUnit.1 hli

theorem exists_cong (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hL : SelfD X L)
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L) :
    ∃ ga : GL (Fin r) E, IsUn X ga ∧
      ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  obtain ⟨U, hU⟩ := isUnit_cols D.proper hL.1 (TensLat.span_of_selfD X hL) h
  obtain ⟨B, hB⟩ := isUnit_cols D.proper X.Λ_fg X.Λ_span D.β_span
  have hA (i) : ((B * U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u i = D.β i := by
    have e1 : u i = (U : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1 := by
      rw [hU]; funext k; simp
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, hB]
    funext k; simp
  choose N hN using fun p : Fin r × Fin r × Fin r =>
    exists_pow_smul (X := X) D.ne_bot (Pi.single p.2.1 (u p.1 p.2.2))
  obtain ⟨ga, hu, s, hs, hb⟩ := _root_.GlobalTheory.UnApprox.weak_approx E r X D.𝔪 D.ne_bot D.cop (B * U⁻¹) (Finset.univ.sup N)
  choose b hb e using hb
  refine ⟨ga, hu, fun i => Lev.cong_iff.2 (Lev.loc_loc hs ?_)⟩
  have e2 : s • ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i - D.β i) =
      ∑ k, ∑ j, b k j • (Pi.single k (u i j) : Fin r → E) := by
    rw [← hA]
    funext k
    simp only [Lev.O_smul, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply,
      Matrix.mulVec, dotProduct, ← e]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k (fun k' _ hk => by rw [if_neg (Ne.symm hk), mul_zero]) (by simp), if_pos rfl]
    change (s : E) * _ = _
    ring
  rw [e2]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    hN (i, k, j) _ (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) (hb k j))

theorem mem_lats (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hΛ : SelfD X X.Λ) (hL : SelfD X L)
    (hu : ∀ i, u i ∈ L) (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L)
    (hc : ∀ i, Cong X D.𝔪 (u i) (D.β i)) : L ∈ D.lats := by
  have h1 : L ≤ Lev.loc D.𝔪 X.Λ := by
    obtain ⟨s, hs, hN⟩ := Lev.nakayama hL.1 h
    intro v hv
    refine Lev.loc_loc hs (Submodule.span_le.2 ?_ (hN v hv))
    rintro _ ⟨i, rfl⟩
    have := add_mem (Lev.loc_mono Submodule.smul_le_right (Lev.cong_iff.1 (hc i)))
      (Lev.le_loc _ (D.β_mem i))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ L ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine Lev.mem_of_loc (D.β_mem i) le_sup_right ?_
    have := add_mem (Lev.loc_mono (le_sup_right (a := L)) (Lev.cong_iff.1 (Lev.cong_symm (hc i))))
      (Lev.le_loc _ (Submodule.mem_sup_left (hu i)))
    rwa [sub_add_cancel] at this
  obtain ⟨s, hs, h1⟩ := Lev.exists_mul_of_fg hL.1 h1
  obtain ⟨t, ht, h2⟩ := Lev.nakayama X.Λ_fg h2
  have h1' (v) (hv : v ∈ L) : Lev.bar t • v ∈ X.Λ := (hΛ.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hL.2 _).1 hv _ (h2 y hy)
  have h2' (v) (hv : v ∈ X.Λ) : Lev.bar s • v ∈ L := (hL.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hΛ.2 _).1 hv _ (h1 y hy)
  obtain ⟨a, b, hab⟩ := Lev.cop_glue D.cop hs (Lev.cop_bar ht)
  obtain ⟨a', b', hab'⟩ := Lev.cop_glue D.cop ht (Lev.cop_bar hs)
  refine ⟨hL, _, Lev.cop_mul hab hab', fun v hv => ?_, fun v hv => ?_⟩
  · rw [mul_comm, mul_smul]
    refine X.Λ.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (X.Λ.smul_mem _ (h1 v hv)) (X.Λ.smul_mem _ (h1' v hv))
  · rw [mul_smul]
    refine L.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (L.smul_mem _ (h2 v hv)) (L.smul_mem _ (h2' v hv))

end GlobalTheory.Dict.Move

theorem GlobalTheory.Dict.exists_move_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (D : SW.Level X) (L : Lt E r) (u : Fin r → Fin r → E), SelfD X X.Λ → SelfD X L → (∀ i, u i ∈ L) → L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L → ∃ ga : GL (Fin r) E, IsUn X ga ∧ mapL ga L ∈ D.lats ∧ ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  intro E _ _ _ r X D L u hΛ hL hu h
  obtain ⟨ga, hun, hc⟩ := Move.exists_cong D hL h
  refine ⟨ga, hun, Move.mem_lats D (u := fun i => Lev.lin ga (u i)) hΛ (Lev.selfD_mapL hun hL)
    (fun i => ⟨_, hu i, rfl⟩) ?_ hc, hc⟩
  refine (Submodule.map_mono (f := Lev.lin ga) h).trans ?_
  rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp, Submodule.map_smul'']
  exact le_rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumns
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Classical Kronecker

namespace GlobalTheory.ColumnSymplectic

variable {n g : ℕ}

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) :
    blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  change (if p.1 = q.1 then τ p.2 q.2 else 0) =
    (1 : Matrix (Fin n) (Fin n) ℂ) p.1 q.1 * τ p.2 q.2
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem blk_mul (A B : Matrix (Fin g) (Fin g) ℂ) : blk n A * blk n B = blk n (A * B) := by
  rw [blk_eq, blk_eq, blk_eq, ← mul_kronecker_mul, one_mul]

theorem blk_one : blk n (1 : Matrix (Fin g) (Fin g) ℂ) = 1 := by
  rw [blk_eq, one_kronecker_one]

theorem blk_mulVec (A : Matrix (Fin g) (Fin g) ℂ) (w : Fin n × Fin g → ℂ) :
    blk n A *ᵥ w = fun p => (A *ᵥ fun i => w (p.1, i)) p.2 := by
  funext p
  simp only [mulVec, dotProduct, blk, of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem blk_mem_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · show (blk n τ)ᵀ = blk n τ
    ext p q
    simp only [transpose_apply, blk, of_apply]
    by_cases e : p.1 = q.1
    · rw [if_pos e.symm, if_pos e]
      exact congrFun (congrFun h.1 p.2) q.2
    · rw [if_neg (Ne.symm e), if_neg e]
  · have e : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ τ.map Complex.im := by
      ext p q
      change Complex.im (if p.1 = q.1 then τ p.2 q.2 else 0) =
        (1 : Matrix (Fin n) (Fin n) ℝ) p.1 q.1 * Complex.im (τ p.2 q.2)
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [e]
    exact PosDef.one.kronecker h.2

private theorem sum_herm_eq_trace_mul_ccT {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G (y k) (y' k) = (y * G * ccT y').trace := by
  simp only [herm, trace, diag, Matrix.mul_apply, ccT, transpose_apply, map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem sum_herm_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (G : Matrix (Fin r) (Fin r) E)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G ((h * y) k) ((h * y') k) = ∑ k, herm G (y k) (y' k) := by
  rw [sum_herm_eq_trace_mul_ccT, sum_herm_eq_trace_mul_ccT, Base.ccT_mul]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, hu, Matrix.mul_one]

theorem sum_EF_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X ((h * y) k) ((h * y') k) = ∑ k, EF X (y k) (y' k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [EF_def, ← map_sum, ← Finset.mul_sum]
  rw [sum_herm_mul hu]

private theorem crd_dotProduct_sub_eq_neg_sum_EF (hs : IsSympl X bas) (Z Z' : Matrix (Fin n) (Fin r) E) :
    (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inl p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inr p.2)) -
      (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inr p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inl p.2)) =
      -∑ k, EF X (Z k) (Z' k) := by
  simp only [EF_crd hs, dotProduct, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_neg,
    ← Finset.sum_sub_distrib]


variable (bas) in
noncomputable def famOf (u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) : Matrix (Fin n) (Fin r) E :=
  Matrix.of fun k => vecQ X bas (Sum.elim (fun i => u.1 (k, i)) fun i => u.2 (k, i))

noncomputable def colMap (hs : IsSympl X bas) (h : Matrix (Fin n) (Fin n) E) :
    ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) →ₗ[ℚ] ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) where
  toFun u := (fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inl p.2),
    fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inr p.2))
  map_add' u v := by
    have : famOf bas (u + v) = famOf bas u + famOf bas v := by
      refine funext fun k => ?_
      change vecQ X bas _ = vecQ X bas _ + vecQ X bas _
      rw [← vecQ_add]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (u + v)) k = (h * famOf bas u) k + (h * famOf bas v) k := fun k => by
      rw [this, Matrix.mul_add]; rfl
    simp only [e, crd_add hs]
    rfl
  map_smul' q u := by
    have : famOf bas (q • u) = q • famOf bas u := by
      refine funext fun k => ?_
      change vecQ X bas _ = q • vecQ X bas _
      rw [← vecQ_smul]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (q • u)) k = q • (h * famOf bas u) k := fun k => by
      rw [this, Matrix.mul_smul]; rfl
    simp only [e, crd_smul hs]
    rfl

theorem colMap_form (hs : IsSympl X bas) {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (u v : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) :
    (colMap hs h u).1 ⬝ᵥ (colMap hs h v).2 - (colMap hs h u).2 ⬝ᵥ (colMap hs h v).1 =
      u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 := by
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  have e1 := crd_dotProduct_sub_eq_neg_sum_EF hs (h * famOf bas u) (h * famOf bas v)
  have e2 := crd_dotProduct_sub_eq_neg_sum_EF hs (famOf bas u) (famOf bas v)
  rw [sum_EF_mul hu, ← e2] at e1
  simp only [hcrd, Sum.elim_inl, Sum.elim_inr] at e1
  exact e1

noncomputable def actM (h : Matrix (Fin n) (Fin n) E) : Matrix (Fin n × Fin g) (Fin n × Fin g) ℂ :=
  blockDiagonal fun i => (rowType X (idx i)).mapMatrix h

theorem actM_mulVec (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    (actM idx h *ᵥ fun p => z p.1 p.2) = fun p => Dict.hAct X idx h z p.1 p.2 := by
  funext p
  simp only [actM, Dict.hAct, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, ite_mul,
    zero_mul, RingHom.mapMatrix_apply, map_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_actM (h : Matrix (Fin n) (Fin n) E) :
    (actM idx h).det = ∏ i, rowType X (idx i) h.det := by
  rw [actM, det_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ => (RingHom.map_det _ _).symm

theorem per_mul (x : Frame X.Ψ r) (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E)
    (k : Fin n) : per X x ((h * y) k) ∘ idx = Dict.hAct X idx h (fun k => per X x (y k) ∘ idx) k := by
  have e : (h * y) k = ∑ k', h k k' • y k' := by
    ext a
    simp [Matrix.mul_apply, Finset.sum_apply]
  funext i
  rw [e, per_sum]
  simp only [Function.comp_apply, Finset.sum_apply, per_smul, Dict.hAct]

theorem conj_mulVec (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    ((blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) =
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  have hH : (hMat X bas idx x)⁻¹ * hMat X bas idx x = 1 :=
    nonsing_inv_mul _ (isUnit_det_hMat (idx := idx) hs hx)
  have e3 : (blk n (hMat X bas idx x)⁻¹ *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) = fun p => z p.1 p.2 := by
    rw [blk_mulVec]
    funext p
    simp only [mulVec_mulVec, hH, one_mulVec]
  rw [← mulVec_mulVec, e3, ← mulVec_mulVec, actM_mulVec, blk_mulVec]

theorem exists_symplectic_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  intro E _ _ _ r X g bas idx n hs _ h hu
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  obtain ⟨s, hsS, hact⟩ := GlobalTheory.SymplecticPeriods.exists_symplectic_action (Fin n × Fin g)
    (colMap hs h) (colMap_form hs hu)
  refine ⟨s, hsS, fun x hx => ?_⟩
  have hT : tauMat X bas idx x ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩
  have hB := blk_mem_siegel (n := n) hT
  have hUnit := isUnit_det_hMat (idx := idx) hs hx
  have key : ∀ u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ),
      (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
          (qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2) =
        qv (colMap hs h u).1 + blk n (tauMat X bas idx x) *ᵥ qv (colMap hs h u).2 := by
    intro u
    have ea : qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2 =
        fun p : Fin n × Fin g =>
          (hMat X bas idx x *ᵥ (fun k => per X x (famOf bas u k) ∘ idx) p.1) p.2 := by
      funext p
      rw [hMat_mulVec_per_crd idx hs hx, Pi.add_apply, blk_mulVec]
      simp only [Pi.add_apply, hcrd, Sum.elim_inl, Sum.elim_inr]
      rfl
    rw [ea, conj_mulVec idx hs hx h (fun k => per X x (famOf bas u k) ∘ idx)]
    funext p
    rw [← per_mul idx x h (famOf bas u) p.1, hMat_mulVec_per_crd idx hs hx, Pi.add_apply,
      Pi.add_apply, blk_mulVec]
    rfl
  obtain ⟨e1, e2⟩ := hact _ hB _ _ hB.1 key
  have hdetM : (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹).det =
      ∏ i, rowType X (idx i) h.det := by
    rw [det_mul, det_mul, mul_right_comm, ← det_mul, blk_mul, mul_nonsing_inv _ hUnit, blk_one,
      det_one, one_mul, det_actM]
  have hdeth : h.det ≠ 0 := by
    have := congrArg Matrix.det hu
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have hP : ∏ i, rowType X (idx i) h.det ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hdeth
  rw [e2, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv'] at hdetM
  have hD : (spDen s (blk n (tauMat X bas idx x))).det ≠ 0 := by
    intro hz
    rw [hz, _root_.inv_zero] at hdetM
    exact hP hdetM.symm
  refine ⟨hT, e1.symm, ?_, fun z => ?_⟩
  · rw [← hdetM, mul_inv_cancel₀ hD]
  · rw [← mulVec_transpose, ← e2]
    exact conj_mulVec idx hs hx h z

end GlobalTheory.ColumnSymplectic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem natCast_mul_X_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (ℓ : LtN Dw n) :
    (N : MvPolynomial (LtN Dw n) c.F) * MvPolynomial.X ℓ ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  obtain ⟨τ, i, j⟩ := ℓ
  refine Subring.subset_closure (Or.inr ⟨τ, i, Pi.single j (N : E), hΛ ?_, ?_⟩)
  · have h1 : (Pi.single j (1 : E) : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n := by
      intro k _
      by_cases hk : k = j
      · subst hk
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hk]
        exact Submodule.zero_mem _
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    have h3 : (N : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = Pi.single j (N : E) := by
      rw [Nat.cast_smul_eq_nsmul, ← Pi.single_nsmul]
      simp
    rwa [h3] at h2
  · unfold letB
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp

theorem exists_natCast_mul_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ) (hN : 0 < N)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (P : MvPolynomial (LtN Dw n) c.F) :
    ∃ M : ℕ, 0 < M ∧ (M : MvPolynomial (LtN Dw n) c.F) * P ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  haveI := c.fin
  induction P using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := c.F) {x}
    have h1 := h x (Finset.mem_singleton_self x)
    have h2 : MvPolynomial.C (y • x) ∈ Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n) :=
      Subring.subset_closure (Or.inl ⟨⟨y • x, h1⟩, rfl⟩)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h3 : (((y * y).natAbs : ℕ) : MvPolynomial (LtN Dw n) c.F) = ((y * y : ℤ) : MvPolynomial (LtN Dw n) c.F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
    have h4 := Subring.mul_mem _ (intCast_mem (Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n)) y) h2
    rw [h3]
    convert h4 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]
    push_cast
    ring
  | add p q hp hq =>
    obtain ⟨M, hM, h⟩ := hp
    obtain ⟨M', hM', h'⟩ := hq
    refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
    have := Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ M') h) (Subring.mul_mem _ (natCast_mem _ M) h')
    convert this using 1
    push_cast
    ring
  | mul_X p ℓ hp =>
    obtain ⟨M, hM, h⟩ := hp
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have := Subring.mul_mem _ h (natCast_mul_X_mem_symO c Λ N hΛ ℓ)
    convert this using 1
    push_cast
    ring

theorem rowHighest_eq_sum_harmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g q0 n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c σ X g q0 n a) (Λ : Lt E n) (N : ℕ), 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∀ Q ∈ Harm.rowHighest ℂ Dc.k Dc.k', ∃ (m : ℕ) (t : Fin m → ℂ) (P : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, P i ∈ harmL c (⟨Λ⟩ : GenLat E n) a) ∧ Q = ∑ i, t i • MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P i)) := by
  intro E _ _ _ H Dw l c σ r g q0 n X a Dc Λ N hN hΛ Q hQ
  obtain ⟨m, t, v, hv⟩ := Submodule.mem_span_set'.1 (Dc.span hQ)
  have hP : ∀ i, ∃ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧
      MvPolynomial.rename Dc.eL (MvPolynomial.map σ P) = (v i).1 := fun i => (v i).2
  choose P hP hPv using hP
  choose M hM hMP using fun i => exists_natCast_mul_mem_symO c Λ N hN hΛ (P i)
  refine ⟨m, fun i => t i / (M i : ℂ), fun i => (M i : MvPolynomial (LtN Dw n) c.F) * P i,
    fun i => ⟨?_, hMP i⟩, ?_⟩
  · have e : (M i : MvPolynomial (LtN Dw n) c.F) * P i = (M i : c.F) • P i := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    change (M i : MvPolynomial (LtN Dw n) c.F) * P i ∈ _
    rw [e]
    exact ⟨Submodule.smul_mem _ _ (hP i).1,
      fun s k k' h u => by rw [map_smul, (hP i).2.1 s k k' h u],
      fun mm hm => (hP i).2.2 mm (MvPolynomial.support_smul hm)⟩
  · rw [← hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : (M i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hM i).ne'
    rw [map_mul, map_mul, map_natCast, map_natCast, hPv, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      div_mul_cancel₀ _ h0]

end GlobalTheory.Dict
end

