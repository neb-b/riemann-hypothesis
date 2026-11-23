module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxFamLinearIndependent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxFamIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor BoxIndep

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {A : Type} {m : ℕ} (β : A → Fin m → O)
    (hβ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β α l = 0) → c = 0) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      ∀ c : (Fin j → Fin m) → F,
        (∀ α : Fin j → A, ∑ a, c a • ∏ i, em i (β (α i) (a i)) = 0) → c = 0 := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, fun c hc => ?_⟩
    have := hc (fun i => i.elim0)
    funext a
    rw [Fintype.sum_unique] at this
    rw [Subsingleton.elim a default]
    simpa using this
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), fun c hc => ?_⟩
    have key : ∀ (α₀ : A) (α : Fin j → A), ∑ l : Fin m, β α₀ l ⊗ₜ[F]
        (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))) = 0 := by
      intro α₀ α
      rw [← hc (Fin.cons α₀ α), ← (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply]
      rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul, TensorProduct.tmul_smul]
    have key2 : ∀ l, (fun a : Fin j → Fin m => c (Fin.cons l a)) = 0 := fun l => h _ fun α => by
      refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
      refine congrFun (hβ (fun l => φ (∑ a : Fin j → Fin m, c (Fin.cons l a) • ∏ i, em i (β (α i) (a i))))
        fun α₀ => ?_) l
      have := congrArg (fun t => TensorProduct.rid F O (LinearMap.lTensor O φ t)) (key α₀ α)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum (LinearMap.lTensor O φ), map_sum (TensorProduct.rid F O), LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, map_zero] using this
    funext a
    have := congrFun (key2 (a 0)) (Fin.tail a)
    simp only [Fin.cons_self_tail] at this
    exact this

variable {X Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {A : Type} {U : A → X.Opens}
    (hx : ∀ α, x ∈ U α) {m : ℕ} (s : ∀ α, Fin m → Γ(X, U α))
    (hs : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p x (c l) * gs (𝟙 X) x (U α) (s α l) = 0) → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z α, r i z ∈ U α) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ (α : Fin j → A) z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U (α i)) (s (α i) (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ (fun α l => gs (𝟙 X) x (U α) (s α l))
    (fun c hc => hs c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this) j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z α => fromSpecStalk_mem x (hx α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · refine h c fun α => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc α z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx _)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_f {D : DegPre R} {K : Type} (S : Finset K) (b : K → Fam D F k) (α : D.X) (jj) :
    ((∑ l ∈ S, b l).s α).f jj = ∑ l ∈ S, ((b l).s α).f jj := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

theorem gs_comb {D : DegPre R} {K : Type} [Fintype K] (c : K → F) (b : K → Fam D F k) (α : D.X) (jj)
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (hz : r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj) :
    gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((∑ l, c l • b l).s α).f jj) =
      ∑ l, germOf (B := CommRingCat.of F) (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c l) *
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) jj) (((b l).s α).f jj) := by
  refine (congrArg _ (sum_f _ _ α jj)).trans ?_
  refine (gs_fsum r z _ hz _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
  refine (gs_mul r z _ hz _ _).trans (congrArg (· * _) ?_)
  exact (gs_res r z le_top hz _).trans
    ((gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem main {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j) {m : ℕ} (b : Fin m → Fam D F k)
    (hb : LinearIndependent F b) (b' : (Fin j → Fin m) → Fam D' F k)
    (hb' : ∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) : LinearIndependent F b' := by
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (TF (R := R) F) D.P.A).left _ hx
    (fun α l => ((b l).s α).f (fun a => J₀ (DegPre.famφ D F α a)))
    (fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
      refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
      rw [Category.id_comp]
      exact hc α) j
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r' : Fin j → (T ⟶ DegPre.BF D F) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ DegPre.BF D' F := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ TF (R := R) F ◁ pD.pw.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ prB pD F i = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (TF (R := R) F) D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun α z => ?_
  obtain ⟨α', rfl⟩ := pD.xe.surjective α
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have hm := hJ'.mem (DegPre.famφ D' F α') (ρ.left : Z ⟶ _)
  have E := (gs_comb c b' α' _ (ρ.left : Z ⟶ _) z hm).symm.trans
    ((congrArg (fun s : Fam D' F k => gs (Y := Z) ρ.left z _ ((s.s α').f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => BoxPhi.fam_val pD (hb' a) α' (Z := Z) ρ.left z hJ hJ'
  simp only [hρ'] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b' a).s α') ρ.left z J' =
      ∏ i, sval ((b (a i)).s (pD.xe α' i)) (r i) z J := ⟨_, E'⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (DegPre.famφ D F (pD.xe α' i)) (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a)))
        (((b l).s (pD.xe α' i)).f (fun a => J₀ (DegPre.famφ D F (pD.xe α' i) a))) =
      v i * sval ((b l).s (pD.xe α' i)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z _) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end BoxFamIndep

theorem boxFam_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m : ℕ) (b : Fin m → Fam D F k), LinearIndependent F b → ∀ b' : (Fin j → Fin m) → Fam D' F k, (∀ a, IsBoxFam pD F k (b' a) (fun i => b (a i))) → LinearIndependent F b' :=
  fun _ _ _ _ _ _ pD _ _ _ _ _ b hb b' hb' => BoxFamIndep.main pD b hb b' hb'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

theorem tri_map {S S' : Scheme.{0}} {G G' : Over S} (f : S' ⟶ S) {E E' T : Over S'} (p : (Over.map f).obj E ⟶ G)
    (p' : (Over.map f).obj E' ⟶ G') (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) (π : G' ⟶ G)
    (h : p'.left ≫ π.left = ρ.left ≫ p.left) :
    (∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p) ∧
      tri f p' x ≫ (π ⊗ₘ π ⊗ₘ π).left = tri f p (fun a => x a ≫ ρ) := by
  have e : ∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p := fun a =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) h).trans
      (Category.assoc _ _ _).symm))
  refine ⟨e, ?_⟩
  show (lift _ (lift _ _) ≫ (π ⊗ₘ π ⊗ₘ π)).left = _
  rw [lift_map, lift_map, e, e, e]

theorem psum_comp {S : Scheme.{0}} {E E' T : Over S} [GrpObj E] [IsCommMonObj E] [GrpObj E'] [IsCommMonObj E']
    (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) [IsMonHom ρ] (k : Finset (Fin 3)) :
    (psum E' x k).left ≫ ρ.left = (psum E (fun a => x a ≫ ρ) k).left :=
  congrArg (fun z => z.left) (psum_hom (MonoidHom.mk' (fun z : T ⟶ E' => z ≫ ρ) fun a b => MonObj.mul_comp a b ρ) x k)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem w_cub_val (U : UnifPre I D A G) (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (y : T.left) {J N} (hJ : Good D.toPre.P.L y J) (hN : Good U.LG.L y N) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) y J =
      (∏ k : thK, Geo.Tor.gw (U.w e) (psum (thickObj R I e G) x k.down).left y
        (J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
        (fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k)) ^ thε k) *
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) y N := by
  have := (U.gt e).q_hom
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl
  exact (clause_iff (tri (thick R I e) (U.gt e).pG x) (tri (thick R I e) (fstG I e G) x)
    (fun k : thK => (psum (thickObj R I e G) x k.down).left) _ _ _ (D.toPre.cub.t.s _) (U.cubG.t.s _)
    (fun k => (U.w e).s (fun _ => J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k),
      fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))) thε).1
    (U.w_cub e T x _ _ (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (hJ.mem _ _) (hN.mem _ _) (fun k => ⟨mem_pull.2 (pt_of_eq (f₄ k) y ▸
      hJ (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)),
      mem_pull.2 (pt_of_eq (f₃ k) y ▸ hN (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))⟩)

theorem cub_box_val (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (e : ℕ)
    {E E' T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (p : (Over.map (thick R I e)).obj E ⟶ D.toPre.P.A)
    (p' : (Over.map (thick R I e)).obj E' ⟶ D'.toPre.P.A) (x : Fin 3 → (T ⟶ E')) (ρ : Fin j → (E' ⟶ E))
    (h : ∀ i, p'.left ≫ (pD.pw.pr i).left = (ρ i).left ≫ p.left) (y : T.left) (J J')
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') :
    (∏ k : thK, om (pr := fun i => (pD.pw.pr i).left) pD.w y J J'
        (tri (thick R I e) p' x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ^ thε k) *
      val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
        (tri (thick R I e) p' x) y J' =
      ∏ i, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) p (fun a => x a ≫ ρ i)) y J := by
  have c := GlobalTheory.CubBox.cubV_box hG R j D.toPre D'.toPre pD ((Over.map (thick R I e)).obj T) y J J' hJ hJ'
    ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p')
  have q := prod_cub ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p') (om (pr := fun i => (pD.pw.pr i).left) pD.w y J J')
  refine (congrArg₂ (· * ·) q rfl).trans ((mul_comm _ _).trans (c.trans (Finset.prod_congr rfl fun i _ => ?_)))
  have t := (tri_map (thick R I e) p p' x (ρ i) (pD.pw.pr i) (h i)).1
  rw [t, t, t]
  rfl

theorem cub_box (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R I e G'))
    (jL : thK → Fin j → U.LG.L.ι) (jM : thK → D'.toPre.P.L.ι)
    (cM : LB.Coh D'.toPre.P.L (fun k => tri (thick R I e) g'.pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM)
    (y : T.left) (hB : tri (thick R I e) g'.pG x y ∈ LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
    (hL : tri (thick R I e) (fstG I e G') x y ∈ LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL) :
    gm (tri (thick R I e) g'.pG x) y (LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
        (D'.toPre.cub.t.s jM) =
      (∏ k : thK, Geo.Tor.gw w' (psum (thickObj R I e G') x k.down).left y (jM k) (fun _ => jL k) ^ thε k) *
      gm (tri (thick R I e) (fstG I e G') x) y (LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL)
        ((boxCub pG U.LG.L U.cubG.t).s jL) := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  let ρ : Fin j → (thickObj R I e G' ⟶ thickObj R I e G) := fun i => (Over.pullback (thick R I e)).map (pG.pr i)
  have ps : ∀ i (k : thK), (psum (thickObj R I e G') x k.down).left ≫ rhoE I pG e i =
      (psum (thickObj R I e G) (fun a => x a ≫ ρ i) k.down).left := fun i k => by
    have := pG.hom i
    exact psum_comp x (ρ i) k.down
  have f₂ := tri_thφ (thick R I e) g'.pG x g'.q rfl
  have f₃ := fun i => tri_thφ (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i) (𝟙 _) (Category.id_comp _).symm
  have f₄ := fun i => tri_thφ (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i) (U.gt e).q rfl
  have hψ : ∀ i a, thφ G' (x3 G') a ≫ (pG.pr i).left = (pG.pr i ⊗ₘ pG.pr i ⊗ₘ pG.pr i).left ≫ thφ G (x3 G) a :=
    fun i a => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).psum_comm a.down
  have t := fun i => (tri_map (thick R I e) (fstG I e G) (fstG I e G') x (ρ i) (pG.pr i) (hρ i).symm).2
  have key := rel_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q hρ hq (K := thK) (ε := thε) y (fun k => (psum (thickObj R I e G') x k.down).left)
    (φ := thφ G (x3 G)) (ψ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ψ' := thφ D'.toPre.P.A (x3 D'.toPre.P.A))
    U.cubG.isGen D.toPre.cub.t D'.toPre.cub.t (tri (thick R I e) g'.pG x)
    (fun i => tri (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i))
    (fun i => tri (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i))
    (fun i k => (congrArg (· ≫ fGl I G e) (ps i k)).trans (f₃ i k).symm) (fun k => (f₂ k).symm)
    (fun i k => (congrArg (· ≫ pGl U e) (ps i k)).trans (f₄ i k).symm)
    (cub_box_val hG pD e (U.gt e).pG g'.pG x ρ hq y)
    (fun i J N hJ hN => (w_cub_val U e T (fun a => x a ≫ ρ i) y hJ hN).trans (congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun k _ => by rw [ps i k]) rfl))
    jL jM cM (Set.mem_iInter.1 hB) (fun k i => by
      have a : ((tri (thick R I e) (fstG I e G') x ≫ thφ G' (x3 G') k) ≫ (pG.pr i).left) y ∈ U.LG.L.U (jL k i) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hL k) i
      rw [Category.assoc, hψ, ← Category.assoc, t] at a
      exact a)
  refine key.trans (congrArg₂ (· * ·) rfl (Eq.trans (Finset.prod_congr rfl fun i _ => ?_)
    (gm_box_pull U.LG.L (fun i => (pG.pr i).left) _ hψ (fun _ => U.cubG.t) _ y jL hL).symm))
  rw [t]

end GlobalTheory.PowUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsoOfIsPowGrp
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
noncomputable def chartPullPullLinComb {X X' Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (pr : K → (X' ⟶ X)) (ε : K → ℤ) (F : Y ⟶ X') (g : Z ⟶ X) (p : K → (Y ⟶ Z))
    (hc : ∀ k, p k ≫ g = F ≫ pr k) :
    ChartPull ((LB.LinComb L pr ε).pull F) (LB.LinComb (L.pull g) p ε) (𝟙 Y) :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L pr ε).pull F).U J ≤
      LB.wchart (L.pull g) p (fun k _ => J PUnit.unit k) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => by
      have h1 : (F ≫ pr k) y ∈ L.U (J PUnit.unit k) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
      rw [← hc k] at h1
      exact h1
  { idx := fun J k _ => J PUnit.unit k
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L pr ε) F (𝟙 Y) y J J' hj hj').trans ?_
      refine (gm_linComb L pr ε (𝟙 Y ≫ F) y _ _ (Set.mem_iInter.1 hj PUnit.unit)
        (Set.mem_iInter.1 hj' PUnit.unit)).trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull g) p ε (𝟙 Y) y _ _ (le J hj) (le J' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L g (𝟙 Y ≫ p k) y _ _ (Set.mem_iInter.1 (le J hj) k)
        (Set.mem_iInter.1 (le J' hj') k)).symm
      rw [Category.assoc, Category.assoc, hc] }

theorem isMonHom_of_isPowGrp {S : Scheme.{0}} {H G' G : Over S} [GrpObj H] [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (f : H ⟶ G') (hf : ∀ i, IsMonHom (f ≫ p.pr i)) : IsMonHom f := by
  have ext : ∀ (a b : H ⊗ H ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  have ext1 : ∀ (a b : 𝟙_ (Over S) ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  constructor
  · refine ext1 _ _ fun i => ?_
    rw [Category.assoc, (hf i).one_hom, (p.hom i).one_hom]
  · refine ext _ _ fun i => ?_
    rw [Category.assoc, (hf i).mul_hom, Category.assoc, (p.hom i).mul_hom, ← Category.assoc (f ⊗ₘ f),
      tensorHom_comp_tensorHom]

theorem exists_iso_of_isPowGrp {S : Scheme.{0}} {H' H G' G : Over S} [GrpObj H'] [GrpObj H]
    [GrpObj G'] [GrpObj G] {j : ℕ} (q : IsPowGrp H' H j) (p : IsPowGrp G' G j) (e : H ≅ G)
    [IsMonHom e.hom] :
    ∃ e' : H' ≅ G', IsMonHom e'.hom ∧ ∀ i, e'.hom ≫ p.pr i = q.pr i ≫ e.hom := by
  let u : H' ⟶ G' := Fan.IsLimit.lift p.lim fun i => q.pr i ≫ e.hom
  let v : G' ⟶ H' := Fan.IsLimit.lift q.lim fun i => p.pr i ≫ e.inv
  have hu : ∀ i, u ≫ p.pr i = q.pr i ≫ e.hom := fun i => Fan.IsLimit.fac p.lim _ i
  have hv : ∀ i, v ≫ q.pr i = p.pr i ≫ e.inv := fun i => Fan.IsLimit.fac q.lim _ i
  have huv : u ≫ v = 𝟙 H' := Fan.IsLimit.hom_ext q.lim _ _ fun i => by
    change (u ≫ v) ≫ q.pr i = 𝟙 H' ≫ q.pr i
    rw [Category.assoc, hv i, ← Category.assoc, hu i, Category.assoc, e.hom_inv_id, Category.comp_id,
      Category.id_comp]
  have hvu : v ≫ u = 𝟙 G' := Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    change (v ≫ u) ≫ p.pr i = 𝟙 G' ≫ p.pr i
    rw [Category.assoc, hu i, ← Category.assoc, hv i, Category.assoc, e.inv_hom_id, Category.comp_id,
      Category.id_comp]
  refine ⟨⟨u, v, huv, hvu⟩, ?_, hu⟩
  refine isMonHom_of_isPowGrp p _ fun i => ?_
  have : IsMonHom (q.pr i) := q.hom i
  change IsMonHom (u ≫ p.pr i)
  rw [hu i]
  infer_instance


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_gen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ gen' : (Over.pullback (jK R)).obj G' ≅ A'.A, IsMonHom gen'.hom ∧ (∀ i, gen'.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ ∃ w : LB.Iso (A'.L.pull gen'.hom.left) ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))), w.IsGen := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  have : IsMonHom U.gen.hom := U.gen_hom
  obtain ⟨p', hp'⟩ := isPowGrp_baseChange _ _ (jK R) G' G j pG
  obtain ⟨e', he', hc⟩ := exists_iso_of_isPowGrp p' pA.toIsPowGrp U.gen
  refine ⟨e', he', fun i => by rw [hc i, hp' i], ?_⟩
  obtain ⟨w0, hw0⟩ := U.ext
  have pullCP : ∀ {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X), ChartPull (L.pull F) L F := fun L F =>
    { idx := fun J => J PUnit.unit
      le := fun J y hy => (mem_pull (L := L) (F := F) (x := y) (J := J)).1 hy
      g := fun y J J' hj hj' => (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp]) }
  have hcA : ∀ k, (p'.pr k).left ≫ U.gen.hom.left = e'.hom.left ≫ (pA.pr k).left := fun k => by
    simpa using (congrArg (fun m => m.left) (hc k)).symm
  have hcG : ∀ k, (p'.pr k).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ (pG.pr k).left := fun k => by
    rw [hp' k]
    simp
  have H34 : LBIso (LB.LinComb (A.L.pull U.gen.hom.left) (fun k => (p'.pr k).left) (fun _ => 1))
      (LB.LinComb (U.LG.L.pull (pullback.fst G.hom (jK R))) (fun k => (p'.pr k).left) (fun _ => 1)) :=
    ⟨LB.linCombIso w0 _ _, linCombIso_isGen w0 hw0 _ _⟩
  have HB : LBIso ((boxLB A.L pA.pr).pull e'.hom.left)
      ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))) :=
    LBIso.chartPull
      (chartPullPullLinComb A.L (fun k => (pA.pr k).left) (fun _ => 1) e'.hom.left U.gen.hom.left
        (fun k => (p'.pr k).left) hcA)
      (chartPullPullLinComb U.LG.L (fun k => (pG.pr k).left) (fun _ => 1) (pullback.fst G'.hom (jK R))
        (pullback.fst G.hom (jK R)) (fun k => (p'.pr k).left) hcG) H34
  have HA : LBIso (A'.L.pull e'.hom.left) ((boxLB A.L pA.pr).pull e'.hom.left) :=
    LBIso.chartPull (pullCP A'.L e'.hom.left) (pullCP _ e'.hom.left) ⟨pA.w, pA.w_gen⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (linComb_isLB _ A.isLB _ _) _)
    (pull_isLB (linComb_isLB _ U.LG.isLB _ _) _) HA HB

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem twisting_statements_of_laws :
    Laws → TwistBaseChangeStatement → TWStatement ∧ FiniteOrderValuationInvariance ∧ PullbackValuationForwardBound := by
  intro hL hT

  have hG : GlobalFnsSt := hL.globalFns
  have hTW : TWStatement := TWM.tw_of hG (twistBCSpan_of hT) _root_.GlobalTheory.RatioVal.main
  exact ⟨hTW, galois_fixed_adelic_matrices_descend hL hTW, pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL)⟩

end GlobalTheory
end

