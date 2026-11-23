module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Linear

open GlobalTheory.EigenSplit

theorem exists_equiv_of_finrank_eq {O K J V V' : Type} [CommRing O] [Field K] [Fintype J] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] [Module.Finite K V] [Module.Finite K V'] {σ : J → O →+* K} (hs : IsSplitting σ)
    (ρ : O →+* Module.End K V) (ρ' : O →+* Module.End K V')
    (h : ∀ i, Module.finrank K (eigenSub ρ (σ i)) = Module.finrank K (eigenSub ρ' (σ i))) :
    ∃ e : V ≃ₗ[K] V', ∀ a x, e (ρ a x) = ρ' a (e x) := by
  classical
  let k : ∀ i, eigenSub ρ (σ i) ≃ₗ[K] eigenSub ρ' (σ i) := fun i => LinearEquiv.ofFinrankEq _ _ (h i)
  refine ⟨(eigenEquiv hs ρ).trans ((LinearEquiv.piCongrRight k).trans (eigenEquiv hs ρ').symm), fun a x => ?_⟩
  obtain ⟨v, rfl⟩ := (eigenEquiv hs ρ).symm.surjective x
  have key : ∀ {W : Type} [AddCommGroup W] [Module K W] (r : O →+* Module.End K W) (v : ∀ i, eigenSub r (σ i)),
      r a ((eigenEquiv hs r).symm v) = (eigenEquiv hs r).symm fun i => σ i a • v i := by
    intro W _ _ r v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eigenEquiv_symm_apply, eigenEquiv_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => mem_eigenSub.1 (v i).2 a
  rw [key]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [key]
  congr 1
  funext i
  exact (k i).map_smul _ _

variable {E : Type} [Field E] [NumberField E]

theorem isSplitting_embeddings : IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
  classical
  obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
  exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
    (by simpa using NumberField.discr_ne_zero E)

def diagRep {g : ℕ} (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lsmul ℂ ℂ (A := Fin g → ℂ) (Fin g → ℂ)).toRingHom.comp
    (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagRep_apply {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) :
    diagRep ty a z = fun i => ty i (a : E) * z i := rfl

theorem finrank_eigenSub_diagRep {g : ℕ} (ty : Fin g → (E →+* ℂ)) (φ : E →+* ℂ) :
    Module.finrank ℂ (eigenSub (diagRep ty) (φ.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = φ} := by
  classical
  have hz : ∀ z ∈ eigenSub (diagRep ty) (φ.comp (algebraMap (𝓞 E) E)), ∀ i, ty i ≠ φ → z i = 0 := by
    intro z hz i hi
    by_contra h0
    refine hi ((isSplitting_embeddings (E := E)).injective (RingHom.ext fun a => ?_))
    exact mul_right_cancel₀ h0 (congrFun (mem_eigenSub.1 hz a) i)
  let r : eigenSub (diagRep ty) (φ.comp (algebraMap (𝓞 E) E)) →ₗ[ℂ] ({i // ty i = φ} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Subtype.val).comp (Submodule.subtype _)
  have hr : Function.Bijective r := by
    refine ⟨(injective_iff_map_eq_zero r).2 fun z h => Subtype.ext (funext fun i => ?_), fun w => ?_⟩
    · by_cases hi : ty i = φ
      · exact congrFun h ⟨i, hi⟩
      · exact hz _ z.2 i hi
    · refine ⟨⟨fun i => if h : ty i = φ then w ⟨i, h⟩ else 0, mem_eigenSub.2 fun a => funext fun i => ?_⟩,
        funext fun i => dif_pos i.2⟩
      rw [diagRep_apply]
      by_cases hi : ty i = φ
      · simp [hi]
      · simp [hi]
  rw [(LinearEquiv.ofBijective r hr).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem exists_hermForm_comp {g g' : ℕ} (Hm : Matrix (Fin g') (Fin g') ℂ) (hH : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Hm'.IsHermitian ∧ ∀ z w, hermForm Hm' z w = hermForm Hm (F z) (F w) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective F
  refine ⟨(M.map star).conjTranspose * Hm * M.map star, Matrix.isHermitian_conjTranspose_mul_mul _ hH, fun z w => ?_⟩
  have e1 : (M.map star).conjTranspose = M.transpose := by ext; simp
  have e2 : star (M.mulVec w) = (M.map star).mulVec (star w) := by
    ext i; simp [Matrix.mulVec, dotProduct]
  simp only [hermForm, Matrix.toLin'_apply]
  rw [e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem linear_eq_zero_of_discrete {g g' : ℕ} (Λ : Submodule ℤ (Fin g' → ℂ)) (hΛ : DiscreteTopology Λ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ z, F z ∈ Λ) : F = 0 := by
  have hc : Continuous fun z => (⟨F z, h z⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  refine LinearMap.ext fun z => ?_
  have e := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa using e

end Linear

section Exp

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale GlobalTheory.EigenSplit

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g g' : ℕ}

def IsExp (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

variable {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

theorem IsExp.zero (he : IsExp e) : e 0 = 1 := by
  have := he.1 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem IsExp.nsmul (he : IsExp e) (n : ℕ) (z : Fin g → ℂ) : e ((n : ℂ) • z) = e z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, he.zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, he.1, ih, pow_succ]

theorem IsExp.comp_equiv (he : IsExp e) (h : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) : IsExp fun z => e (h z) := by
  have hd : ∀ w v, IsDerivAt0 (fun z => (e (h z)).left) w v ↔ IsDerivAt0 (fun z => (e z).left) (h w) v :=
    fun w v => deriv_linear he.2.2.1 h.toLinearMap
  refine ⟨fun z w => by simp only [map_add (f := _), he.1 _ _], he.2.1.comp h.surjective, isHolTo_linear he.2.2.1 h.toLinearMap,
    fun w => ?_, fun v hv => ?_⟩
  · simp only [hd]
    exact he.2.2.2.1 (h w)
  · simp only [hd]
    simp only [map_zero] at hv
    exact (h.toEquiv.existsUnique_congr_left (p := fun w => IsDerivAt0 (fun z => (e z).left) (h w) v.left)).2
      (by simpa using he.2.2.2.2 v hv)

variable {O : Type} [CommRing O] (act : OAct O G)

theorem IsExp.exists_rep (he : IsExp e) (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : DiscreteTopology Λ)
    (hker : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hF : ∀ a, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e (F z) = e z ≫ act.act a) :
    ∃ ρ : O →+* Module.End ℂ (Fin g → ℂ), ∀ a z, e (ρ a z) = e z ≫ act.act a := by
  choose F hF using hF
  have hu : ∀ A B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, e (A z) = e (B z)) → A = B := fun A B h => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete Λ hΛ _ fun z => (hker _).1 ?_)
    have := he.1 ((A - B) z) (B z)
    rw [LinearMap.sub_apply, sub_add_cancel, h] at this
    exact mul_eq_right.1 this.symm
  refine ⟨RingHom.mk' ⟨⟨F, hu _ _ fun z => ?_⟩, fun a b => hu _ _ fun z => ?_⟩ fun a b => hu _ _ fun z => ?_, hF⟩
  · rw [hF, act.one, Category.comp_id]; rfl
  · show e (F (a * b) z) = e (F a (F b z))
    rw [hF, hF, hF, mul_comm, act.mul, Category.assoc]
  · show e (F (a + b) z) = e (F a z + F b z)
    rw [he.1, hF, hF, hF, act.add, MonObj.comp_mul]

theorem IsExp.finrank_eigenSub (he : IsExp e) (ρ : O →+* Module.End ℂ (Fin g → ℂ))
    (hρ : ∀ a z, e (ρ a z) = e z ≫ act.act a) {τ : O →+* ℂ} {n : ℕ} (hn : LieMult act y τ n) :
    Module.finrank ℂ (eigenSub ρ τ) = n := by
  choose d hd hu using he.2.2.2.1
  have h0 : (e 0).left = (1 : Over.mk y ⟶ G).left := by rw [he.zero]
  have hinj : Function.Injective d := fun w w' h =>
    (he.2.2.2.2 (d w) (hd w).1).unique (hd w) (h ▸ hd w')
  have hadd : ∀ w w', d (w + w') = d w * d w' := fun w w' => (hu _ _ (deriv_mul h0 (hd w) (hd w'))).symm
  have hsm : ∀ c w, epsPtScale y c ≫ d w = d (c • w) := fun c w => hu _ _ (deriv_smul (hd w) c)
  have hact : ∀ a w, d w ≫ act.act a = d (ρ a w) := fun a w => hu _ _ (by
    refine (deriv_linear he.2.2.1 (ρ a)).1 ?_
    simp only [hρ]
    exact deriv_comp (hd w) (act.act a).left)
  have hz : d 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hsum : ∀ (m : ℕ) (w : Fin m → Fin g → ℂ), (List.ofFn fun i => d (w i)).prod = d (∑ i, w i) := by
    intro m
    induction m with
    | zero => intro w; simp [hz]
    | succ m ih => intro w; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have heig : ∀ w, Eig (epsPtZero y) (epsPtScale y) act.act τ (d w) ↔ w ∈ eigenSub ρ τ := fun w => by
    rw [mem_eigenSub, Eig, and_iff_right (Over.OverMorphism.ext ((hd w).1.trans h0))]
    simp only [hact, hsm, hinj.eq_iff]
  obtain ⟨v, hv, h⟩ := (lieMult_iff y act τ n).1 hn
  have : ∀ i, ∃ w, v i = d w := fun i => by
    obtain ⟨w, hw, -⟩ := he.2.2.2.2 (v i) ((congrArg (·.left) (hv i).1).trans h0.symm)
    exact ⟨w, hu _ _ hw⟩
  choose w hw using this
  obtain rfl : v = fun i => d (w i) := funext hw
  let L : (Fin n → ℂ) →ₗ[ℂ] eigenSub ρ τ := Fintype.linearCombination ℂ fun i => ⟨w i, (heig _).1 (hv i)⟩
  have hL : Function.Bijective L := (Function.bijective_iff_existsUnique _).2 fun x => by
    refine (existsUnique_congr fun c => ?_).1 (h _ ((heig x.1).2 x.2))
    simp only [hsm, hsum, hinj.eq_iff]
    rw [eq_comm, Subtype.ext_iff]
    simp [L, Fintype.linearCombination_apply]
  rw [← (LinearEquiv.ofBijective L hL).finrank_eq, Module.finrank_fin_fun]

theorem isExp_push {G' : Over (Sp ℂ)} [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G y φ)
    {L : LB G'.left} (u : HolUnif G' L g) (h1 : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h2 : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (Φ : (𝟙_ (Over (Sp ℂ)) ⟶ G') ≃* (Over.mk y ⟶ G))
    (hΦ : ∀ x, (Φ x).left = x.left ≫ φ) : IsExp fun z => Φ (u.ex z) := by
  have hd : ∀ w (v : epsR ℂ ⟶ G'), IsTangent v → u.IsDiff w v →
      IsDerivAt0 (fun z => (Φ (u.ex z)).left) w (v.left ≫ φ) := fun w v hv hw => by
    simp only [hΦ]
    exact deriv_comp (e := fun z => (u.ex z).left) ⟨tangent_comp hv, hw⟩ φ
  let Ψ : (epsR ℂ ⟶ G') ≃* (epsPt y ⟶ G) := ObjPull.pushEquiv hφ (epsR ℂ)
  refine ⟨fun z w => by simp only [u.ex_add, map_mul], Φ.surjective.comp u.ex_onto, ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [hΦ]
    refine isHolTo_comp (e := fun z => (u.ex z).left) (fun U f => ?_) φ
    simp only [Set.mem_univ, true_and]
    exact u.hol U f
  · obtain ⟨v, ⟨hv, hw⟩, -⟩ := h2 w
    exact ⟨Ψ v, hd w v hv hw, fun v' hv' => Over.OverMorphism.ext (deriv_unique hv' (hd w v hv hw))⟩
  · obtain ⟨v, rfl⟩ := Ψ.surjective v
    have ht : IsTangent v := by
      refine hφ.1.hom_ext ?_ ?_
      · rw [← ex_zero_left u, ← hΦ, ← hv, Category.assoc]; rfl
      · rw [Category.assoc, Over.w v, Over.w η[G']]
        show Spec.map _ ≫ Spec.map _ = 𝟙 _
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
    obtain ⟨w, hw, hwu⟩ := h1 v ht
    refine ⟨w, hd w v ht hw, fun w' hw' => hwu w' ?_⟩
    obtain ⟨v', ⟨hv', hw''⟩, -⟩ := h2 w'
    obtain rfl : v = v' := Ψ.injective (Over.OverMorphism.ext (deriv_unique hw' (hd w' v' hv' hw'')))
    exact hw''

end Exp

section Tate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {act : OAct (𝓞 E) G} {L : LB G.left}
  {ty : Fin g → (E →+* ℂ)}

theorem exp_div_smul {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {P : La →+ (Fin g → ℂ)}
    (hP : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a) (c : ℂ) (a : 𝓞 E) (x : La) :
    e (c • P (a • x)) = e (c • P x) ≫ act.act a := by
  rw [← hlin]
  congr 1
  funext k
  simp only [Pi.smul_apply, hP, smul_eq_mul]
  ring

theorem exp_div_pow {La : Type} [AddCommGroup La] {P : La →+ (Fin g → ℂ)} (he : IsExp e)
    (hker : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) (x : La) : e ((n : ℂ)⁻¹ • P x) ^ n = 1 := by
  rw [← he.nsmul, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne'), hker]
  exact ⟨x, rfl⟩

theorem adj_of_tateIso {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {P : La →+ (Fin g → ℂ)}
    {EF : LinearMap.BilinForm ℤ La} (hL : L.IsLB) (he : IsExp e) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hP : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a)
    (hweil : ∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    {D : Datum H} (I : TateIso D ℂ (Over.mk y ⟶ G) (fun a x => x ≫ act.act a)
      (fun n x x' c => Out.WeilIs G L n x x' (unitOn c))) (c : 𝓞 E) (x x' : La) :
    EF (c • x) x' = EF x (H.bar c • x') := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ EF (c • x) x' - EF x (H.bar c • x') := fun n hn => by
    obtain ⟨a, ha⟩ := (I.onto n hn _).1 (exp_div_pow he hker hn x)
    obtain ⟨b, hb⟩ := (I.onto n hn _).1 (exp_div_pow he hker hn x')
    have e1 := I.isom n hn (c • a) b
    have e2 := I.isom n hn a (H.bar c • b)
    rw [I.lin, ha, hb, ← exp_div_smul hP hlin] at e1 e2
    have f1 := weilIs_unique_fieldPoint _ _ _ hL ℂ _ _ _ _ _ _ e1 (hweil n _ _ _ hn (expNegUnit_zpow_val n _))
    have f2 := weilIs_unique_fieldPoint _ _ _ hL ℂ _ _ _ _ _ _ e2 (hweil n _ _ _ hn (expNegUnit_zpow_val n _))
    rw [← (expNegUnit_isPrimitiveRoot hn).zpow_eq_one_iff_dvd, zpow_sub, ← f1, ← f2, D.adj, mul_inv_cancel]
  exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key _ (Nat.succ_pos (EF (c • x) x' - EF x (H.bar c • x')).natAbs))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))

def expTateIso {D : Datum H} {P : D.La →+ (Fin g → ℂ)} (he : IsExp e) (hP : IsPeriod D ty P)
    (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a)
    (hweil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    TateIso D ℂ (Over.mk y ⟶ G) (fun a x => x ≫ act.act a) (fun n x x' c => Out.WeilIs G L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := e ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add (f := _), smul_add, he.1]
  lin n c a := exp_div_smul hP.1 hlin _ c a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [hker]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := he.2.1 x
      rw [← he.nsmul, hker] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      exact exp_div_pow he hker hn a
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← he.nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hweil n a b _ hn (expNegUnit_zpow_val n _)

theorem similar_with_multiplier {D D' : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {ac : 𝓞 E → Q → Q}
    {w : ℕ → Q → Q → kˣ → Prop} (hw : ∀ n x y c c', w n x y c → w n x y c' → c = c')
    (I : TateIso D k Q ac w) (I' : TateIso D' k Q ac w) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n) ∧
      ∀ n m : ℕ, 0 < m → n ∣ m → ∀ a, I.ev n a = I'.ev n (f m a) := by
  obtain ⟨f, -, h1, h2, -, -, -, hf⟩ := tateIso_similar_of_two_data hw I I'
  have h3 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose ν hν using h3
  refine ⟨f, ν, h1, h2, fun n hn a b => ?_, hν, ?_⟩
  · have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := hw n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rintro n _ hm ⟨m, rfl⟩ a
    have hn := Nat.pos_of_mul_pos_right hm
    have hm' := Nat.pos_of_mul_pos_left hm
    rw [← I.tower n m hn hm', hf _ hm, I'.tower n m hn hm']

end Tate

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (T : Over S')
    (hW : ∀ (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
      y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c))
    (t : T.left ⟶ S) (ht : T.hom ≫ f = t) :
    ∃ Φ : (T ⟶ G') ≃* (Over.mk t ⟶ G), (∀ x, (Φ x).left = x.left ≫ φ) ∧
      ∀ (k : ℤ) x y c, Out.WeilIs G' L' k x y c → Out.WeilIs G L k (Φ x) (Φ y) c := by
  subst ht
  exact ⟨ObjPull.pushEquiv h T, fun _ => rfl, fun k x y c => (hW k x y _ _ c rfl rfl).1⟩

end GlobalTheory.PointUnif
