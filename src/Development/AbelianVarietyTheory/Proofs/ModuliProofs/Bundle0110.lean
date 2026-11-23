module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleOfFiniteQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.QuotTriple

open GlobalTheory.CechPic

theorem isPullback_lift {X X' : Scheme.{0}} {π : X ⟶ X'} {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left}
    {b : Q.left ⟶ Q'.left} (ha : IsPullback a P.hom P'.hom π) (hb : IsPullback b Q.hom Q'.hom π) :
    IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (P ⊗ Q).hom (P' ⊗ Q').hom π := by
  have big : IsPullback ((snd P Q).left ≫ b) (fst P Q).left Q'.hom (P.hom ≫ π) :=
    (IsPullback.of_hasPullback P.hom Q.hom).flip.paste_horiz hb
  have e₁ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (fst P' Q').left = (fst P Q).left ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have e₂ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (snd P' Q').left = (snd P Q).left ≫ b :=
    congrArg (fun z => z.left) (lift_snd (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have h₁ : IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (fst P Q).left
      (fst P' Q').left a := by
    refine IsPullback.of_right (h₁₂ := (snd P' Q').left) (v₁₃ := Q'.hom) (h₂₂ := P'.hom) ?_ e₁
      (IsPullback.of_hasPullback P'.hom Q'.hom).flip
    rw [e₂, ha.w]
    exact big
  exact h₁.paste_vert ha

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pull_cls_cube (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hc : pull φ (cls L hL) = cls L' hL') {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    pull U.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = cls (cubeLB G' x' L') (LB.isLB_linComb hL' _ _) := by
  refine (congrArg (pull U.left) (cls_linComb hL _ _ _)).trans (Eq.trans ?_ (cls_linComb hL' _ _ _).symm)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← hc, ← pull_comp]
  exact congrArg (fun q => _ • pull q (cls L hL)) (psum_push h x' x U hx I.down).symm

theorem psum_one {T : Over S} {n : ℕ} (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg ((1 : T ⟶ G) * ·) ih).trans (_root_.mul_one _)

theorem one_left : (1 : 𝟙_ (Over S) ⟶ G).left = eSec G := by
  rw [Hom.one_def]; simp [eSec]

theorem pull_cls_cube_origin {L : LB G.left} (hL : L.IsLB) (h0 : pull (eSec G) (cls L hL) = 0) {T : Over S} {n : ℕ}
    (x : Fin n → (T ⟶ G)) (o : 𝟙_ (Over S) ⟶ T) (ho : ∀ i, o ≫ x i = 1) :
    pull o.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = 0 := by
  refine (congrArg (pull o.left) (cls_linComb hL _ _ _)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  have e : o ≫ psum G x I.down = 1 :=
    (psum_hom (preHom o) x I.down).trans ((congrArg (fun z => psum G z I.down) (funext ho)).trans (psum_one _))
  rw [map_zsmul, ← pull_comp, ← Over.comp_left, e, one_left, h0, smul_zero]

end Cube

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'}

theorem eq_zero_of_pull (hq : IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens,
      Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
        ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom)
    {P : Over X} {P' : Over X'} {Φ : P.left ⟶ P'.left} (hΦ : IsPullback Φ P.hom P'.hom π) (hs' : Smooth P'.hom)
    (hs : Smooth P.hom) (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P)
    (o : 𝟙_ (Over X) ⟶ P) (o' : 𝟙_ (Over X') ⟶ P') (ho : o.left ≫ Φ = π ≫ o'.left) (c : Pic P'.left)
    (h₀ : pull o'.left c = 0) (h₁ : pull Φ c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (exists_gen_of_quotient_of_rigid Γ X X' ρ π P P' Φ o.left o'.left N hq hΦ
    inferInstance (Over.w o) (Over.w o') ho
    (eq_one_of_appLE_section_eq_one X P o.left (Over.w o) hs hg ⟨hr, hab⟩) hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁))

theorem genericPoints_subset_image [Surjective π] : genericPoints X' ⊆ π '' genericPoints X := by
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  let C : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
  have hs : (genericPoints.ofComponent C).1 ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  exact ⟨_, (genericPoints.ofComponent C).2, eq_of_specializes_of_mem_genericPoints hy (hs.map π.continuous)⟩

end Quot

theorem exists_sab_of_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  intro E _ _ _ H Γ _ _ X X' ρ π t G' _ _ a' φ L' hq ⟨hr, hab⟩ hG' gp hact hL' hiso
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  have hr' : IsReduced X' := ⟨fun V => isReduced_of_injective _ (hq.2.2 V).1⟩
  have hab' : genericPoints X' ⊆ abLocus G' := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := genericPoints_subset_image (π := π) hy
    exact (abLocus_pullback abLocusOne hG' gp.1 x).2 (hab hx)
  have he : eSec t.G ≫ φ = π ≫ eSec G' := (cubeMapOf gp).e_comm
  have hp : eSec G' ≫ G'.hom = 𝟙 X' := Over.w _
  have c₀ : pull (eSec t.G) (cls t.PP.L t.PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
  have cl : cls t.PP.L t.PP.isLB = pull φ (cls L' hL') := (cls_eq_iff _ (pull_isLB hL' φ)).2 hiso
  obtain ⟨M, hM, cM⟩ := cls_surj (cls L' hL' - pull (G'.hom ≫ eSec G') (cls L' hL'))
  have m₀ : pull (eSec G') (cls M hM) = 0 := by
    have e : eSec G' ≫ G'.hom ≫ eSec G' = eSec G' :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G') hp).trans (Category.id_comp _))
    rw [cM, map_sub, ← pull_comp, e, sub_self]
  have m₁ : pull φ (cls M hM) = cls t.PP.L t.PP.isLB := by
    have e : φ ≫ G'.hom ≫ eSec G' = t.G.hom ≫ eSec t.G ≫ φ := by
      rw [he, ← Category.assoc, gp.1.w, Category.assoc]
    rw [cM, map_sub, ← pull_comp, e, pull_comp, pull_comp, ← cl, c₀, map_zero, sub_zero]
  obtain ⟨r, hrig⟩ := (cls_eq_zero_iff (pull_isLB hM (eSec G'))).1 m₀
  let PP : RigLB G' := ⟨M, r, hM, hrig⟩
  have a₁ := t.semi.smooth
  have := t.semi.geomConnected
  have b₁ := grpObj_geometricallyIntegral_of_smooth X t.G
  obtain ⟨a₂, b₂, c₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G t.G a₁ a₁ b₁ b₁
  have d₂ := (Set.subset_inter hab hab).trans c₂
  obtain ⟨a₃, b₃, c₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G _ a₁ a₂ b₁ b₂
  have d₃ := (Set.subset_inter hab d₂).trans c₃
  have a₁' := hG'.smooth
  have a₂' : Smooth (G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have a₃' : Smooth (G' ⊗ G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have p₂ := isPullback_lift gp.1 gp.1
  have p₃ := isPullback_lift gp.1 p₂
  have o₁ : (1 : 𝟙_ (Over X) ⟶ t.G).left ≫ φ = π ≫ (1 : 𝟙_ (Over X') ⟶ G').left := by
    rw [one_left, one_left]; exact he
  have pa : ∀ {T : Over X} (x : T ⟶ t.G) a, pushPt gp.1.w (x ≫ t.act.act a) = pushPt gp.1.w x ≫ a'.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ol : ∀ {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left} {b : Q.left ⟶ Q'.left}
      (wa : a ≫ P'.hom = P.hom ≫ π) (wb : b ≫ Q'.hom = Q.hom ≫ π) (u : 𝟙_ _ ⟶ P) (v : 𝟙_ _ ⟶ Q) (u' : 𝟙_ _ ⟶ P')
      (v' : 𝟙_ _ ⟶ Q'), u.left ≫ a = π ≫ u'.left → v.left ≫ b = π ≫ v'.left →
      (lift u v).left ≫ (lift (pushPt wa (fst P Q)) (pushPt wb (snd P Q))).left = π ≫ (lift u' v').left := by
    intro P Q P' Q' a b wa wb u v u' v' hu hv
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst P' Q').left = (_ ≫ _) ≫ (fst P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ← hu]
      show _ ≫ (fst P Q).left ≫ a = _
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ _) ≫ (snd P' Q').left = (_ ≫ _) ≫ (snd P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hv]
      show _ ≫ (snd P Q).left ≫ b = _
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  have o₂ := ol gp.1.w gp.1.w 1 1 1 1 o₁ o₁
  have o₃ := ol gp.1.w p₂.w 1 _ 1 _ o₁ o₂
  have aone : ∀ a, (1 : 𝟙_ (Over X') ⟶ G') ≫ a'.act a = 1 := fun a => by
    have := a'.hom a
    exact MonObj.one_comp _
  have hΘ : ∃ s : (Theta G' M).Gen, s.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 (eq_zero_of_pull hq p₃ a₃' a₃ b₃ hr d₃ _ _ o₃ _
      (pull_cls_cube_origin hM m₀ (x3 G') _ fun i => by fin_cases i <;> simp [x3])
      ((pull_cls_cube gp hM t.PP.isLB m₁ (x3 t.G) (x3 G') _ fun i => ?_).trans
        ((cls_eq_zero_iff _).2 ⟨_, t.cub.isGen⟩)))
    fin_cases i
    · simp [x3]
    · refine Eq.trans ?_ (congrArg (· ≫ fst G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_fst (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
    · refine Eq.trans ?_ (congrArg (· ≫ snd G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_snd (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
  have hsym : LBIso M (M.pull (GrpObj.inv (X := G')).left) := by
    have e₁ : φ ≫ (GrpObj.inv (X := G')).left = (GrpObj.inv (X := t.G)).left ≫ φ := by
      have e := congrArg (fun z => z.left) (map_inv (pushHom gp t.G) (𝟙 t.G))
      exact (congrArg (· ≫ (GrpObj.inv (X := G')).left) (Category.id_comp φ).symm).trans
        (e.symm.trans (congrArg (· ≫ φ) (Category.id_comp _)))
    have e₂ : (1 : 𝟙_ (Over X') ⟶ G') ≫ GrpObj.inv (X := G') = 1 := inv_one (G := 𝟙_ (Over X') ⟶ G')
    obtain ⟨-, w, hw, -⟩ := t.sym
    have e₃ : cls t.PP.L t.PP.isLB = pull (GrpObj.inv (X := t.G)).left (cls t.PP.L t.PP.isLB) :=
      (cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    refine (cls_eq_iff hM (pull_isLB hM _)).1 (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, cls_pull hM, ← pull_comp, ← Over.comp_left, e₂, sub_self]
    · rw [map_sub, cls_pull hM, ← pull_comp, e₁, pull_comp, m₁, ← e₃, sub_self]
  have hadj : ∀ a, LBIso (cubeLB G' ![fst G' G' ≫ a'.act a, snd G' G'] M)
      (cubeLB G' ![fst G' G', snd G' G' ≫ a'.act (H.bar a)] M) := fun a => by
    refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq p₂ a₂' a₂ b₂ hr d₂ _ _ o₂ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero]
      refine (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).trans
        (((cls_eq_iff _ _).2 (t.adj a)).trans (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp)
        · simp
      · fin_cases i
        · simp
        · exact (pa _ _).trans (by simp)
  have hprim : LBIso M (cubeLB G' ![𝟙 G', a'.act H.w0] M) := by
    refine (cls_eq_iff hM (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (one_left (G := G') ▸ m₀).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero, m₁]
      refine ((cls_eq_iff _ (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (Eq.trans
        (pull_cls_cube gp hM t.PP.isLB m₁ _ ![𝟙 G', a'.act H.w0] (pushPt gp.1.w (𝟙 t.G)) fun i => ?_).symm ?_)
      · fin_cases i
        · simp
        · exact (congrArg (pushPt gp.1.w) (Category.id_comp _).symm).trans (pa _ _)
      · exact congrArg (fun q => pull q _) (Category.id_comp φ)
  obtain ⟨k₁, k₂⟩ := CubeGen.cubical_and_symmetric X' G' PP hG' ⟨hr', hab'⟩
  obtain ⟨cub⟩ := k₁ hΘ
  let t' : SAB H X' := ⟨G', hG', a', PP, cub, k₂ hsym, hadj, hprim⟩
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H X' X t' t π φ ⟨hr, hab⟩ gp hact
    ((cls_eq_iff _ (pull_isLB hM φ)).1 m₁.symm)
  exact ⟨t', ν, Iso.refl _, (Category.comp_id _).trans hν⟩

end GlobalTheory.QuotTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelDescent

section Points

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem isPullback_square (hA : IsPullback φ G'.hom G.hom f) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h : IsSquare φ φ₂) : IsPullback φ₂ (G' ⊗ G').hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have v₂ : (snd G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ G'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lift_square {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) {T : Over S'} {T₀ : Over S}
    {τ : T.left ⟶ T₀.left} {a b : T ⟶ G'} {a₀ b₀ : T₀ ⟶ G} (ha : a.left ≫ φ = τ ≫ a₀.left)
    (hb : b.left ≫ φ = τ ≫ b₀.left) : (lift a b).left ≫ φ₂ = τ ≫ (lift a₀ b₀).left := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
    rw [Category.assoc, h.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
      lift_fst, ha]
  · change (_ ≫ _) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
    rw [Category.assoc, h.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
      lift_snd, hb]

variable [GrpObj G] [GrpObj G']

theorem exists_liftHom (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) :
    ∃ ρ : (T₀ ⟶ G) →* (T ⟶ G'), ∀ x₀ x, ρ x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := by
  let r : (T₀ ⟶ G) → (T ⟶ G') := fun x₀ => Over.homMk
    (h.1.lift (τ ≫ x₀.left) T.hom (by rw [Category.assoc, Over.w, hτ])) (h.1.lift_snd _ _ _)
  have hr : ∀ x₀, (r x₀).left ≫ φ = τ ≫ x₀.left := fun x₀ => h.1.lift_fst _ _ _
  have key : ∀ x₀ x, r x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := fun x₀ x =>
    ⟨fun e => e ▸ hr x₀, fun e => Over.OverMorphism.ext
      (h.1.hom_ext ((hr x₀).trans e.symm) (by rw [Over.w, Over.w]))⟩
  let U : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ hτ
  refine ⟨MonoidHom.mk' r fun a b => (key _ _).2 ?_, key⟩
  rw [← h.2 T (r a) (r b) (U ≫ a) (U ≫ b) (hr a).symm (hr b).symm, ← MonObj.comp_mul]
  rfl

theorem one_comp (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) : (1 : T ⟶ G').left ≫ φ = τ ≫ (1 : T₀ ⟶ G).left := by
  obtain ⟨ρ, hρ⟩ := exists_liftHom h T T₀ τ hτ
  exact (hρ _ _).1 (map_one ρ)


omit [GrpObj G'] in
theorem weilIs_congr {X : Scheme.{0}} {a b : X ⟶ S} (e : a = b) (L : LB G.left) (k : ℤ)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst e
  rw [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]
  exact H

end Points

section Bundles

variable {X X₀ Y Y₀ : Scheme.{0}}

theorem lbIso_square {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB) {F : X ⟶ X₀} (hw : LBIso P (P₀.pull F))
    {a : Y ⟶ X} {a₀ : Y₀ ⟶ X₀} {ψ : Y ⟶ Y₀} (e : a ≫ F = ψ ≫ a₀) : LBIso (P.pull a) ((P₀.pull a₀).pull ψ) :=
  LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ (ψ ≫ a₀)) (pull_isLB (pull_isLB hP₀ _) _)
    (LBIso.chartPull (chartPullPull P a a rfl) (chartPullSame P₀ _ _ _ a fun _ => e.symm) hw)
    (LBIso.chartPull (chartPullSame P₀ _ _ _ ψ fun _ => rfl) (chartPullPull _ ψ ψ rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hP₀ a₀)))

theorem exists_gen_of_lbIso {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

end Bundles

theorem prod_zpow_single {I H : Type} [Fintype I] [DecidableEq I] [CommGroup H] (l : (I → ℤ) → H)
    (hl : ∀ a b, l (a + b) = l a * l b) (a : I → ℤ) : ∏ u, l (Pi.single u 1) ^ a u = l a := by
  let F : (I → ℤ) →+ Additive H := AddMonoidHom.mk' (fun a => Additive.ofMul (l a)) fun a b => by
    rw [hl, ofMul_mul]
  have e : a = ∑ u, a u • (Pi.single u 1 : I → ℤ) := by
    ext v
    simp [Finset.sum_apply, Pi.single_apply]
  have : F a = ∑ u, a u • F (Pi.single u 1) := by
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  apply Additive.ofMul.injective
  rw [ofMul_prod]
  simp only [ofMul_zpow]
  exact this.symm

end GlobalTheory.SiegelDescent

namespace GlobalTheory

open SiegelDescent

theorem exists_siegPre_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c A₀ _ φ φ₂ P₀ lev₀ hs hp sq hP₀ hw hlev
  have ab : IsAbelianScheme A₀ := (_root_.GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₀ K i A₀ c.A φ hp c.ab).1
  haveI := ab.comm
  haveI := ab.smooth
  haveI := ab.proper
  haveI := ab.geomConnected
  have epi : ∀ (F F' : Type) [Field F] [Field F'] (j : F →+* F'), Epi (spMap j) := fun F F' _ _ j =>
    ((_root_.GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff F F' j).1 _ _ (𝟙 _) (𝟙 _) (spMap j) (IsPullback.of_vert_isIso ⟨by simp⟩)).1
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ spMap i := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have gen := (_root_.GlobalTheory.lb_gen_iso_descend_field K₀ K i _ _ A₀.hom c.A.hom φ inferInstance inferInstance inferInstance hp.1).1
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      (∃ t : (c.P.pull a.left).Gen, t.IsGen) → ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := fun a a₀ e ht =>
    gen _ (pull_isLB hP₀ _) (exists_gen_of_lbIso (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _)
      (lbIso_square c.isLB hP₀ hw e) ht)
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have h₁ : Smooth (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₂ : IsProper (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₃ : GeometricallyConnected (A₀ ⊗ A₀).hom := by
      rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
    refine (_root_.GlobalTheory.lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (c.A ⊗ c.A).hom φ₂ h₁ h₂ h₃ (isPullback_square hp.1 φ₂ sq)).2 _ _ hP₀
      (pull_isLB hP₀ _) ?_
    exact LBIso.trans (pull_isLB hP₀ _) c.isLB (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans c.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _) c.symm
        (lbIso_square c.isLB hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρ, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) (spMap i)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K₀)) ⟶ A₀) := fun a => ∏ u, lev₀ u ^ a u
  have ρlev : ∀ a, ρ (lev a) = c.lev a := fun a => by
    rw [← prod_zpow_single c.lev c.lev_add a]
    refine (map_prod ρ _ _).trans (Finset.prod_congr rfl fun u _ => ?_)
    rw [map_zpow, (hρ _ _).2 (hlev u)]
  have hlev' : ∀ a, (c.lev a).left ≫ φ = spMap i ≫ (lev a).left := fun a => (hρ _ _).1 (ρlev a)
  have ρinj : Function.Injective ρ := fun x y e => by
    haveI := epi _ _ i
    exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1
      (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) c.rig₂
            symm := symm, lev := lev
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev'⟩
  intro k _ _ x β z hx hz
  obtain ⟨i', rfl⟩ : ∃ i' : K₀ →+* k, x = spMap i' := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain ⟨Ω, _, _, j, j', hj⟩ := exists_algClosed_join_of_two_field_extensions K₀ K k i i'
  have e : spMap j' ≫ spMap i' = spMap j ≫ spMap i := by rw [← spMap_comp, ← spMap_comp, hj]
  obtain ⟨g₁, g₂, g₃⟩ := c.geom Ω (spMap j) (j'.comp β) (Units.map j'.toMonoidHom z)
    (by rw [hs, ← Category.assoc, ← e, Category.assoc, hx, spMap_comp]) (congrArg j' hz)
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk (spMap j)) (Over.mk (spMap i')) (spMap j') e
  have σinj : Function.Injective σ := fun x y e => by
    haveI := epi _ _ j'
    exact Over.OverMorphism.ext ((cancel_epi (spMap j')).1
      (((hσ x _).1 rfl).symm.trans ((hσ y _).1 e.symm)))
  have pt : ∀ a, (toUnit (Over.mk (spMap j)) ≫ c.lev a).left ≫ φ =
      spMap j' ≫ (toUnit (Over.mk (spMap i')) ≫ lev a).left := fun a => by
    change (spMap j ≫ (c.lev a).left) ≫ φ = spMap j' ≫ spMap i' ≫ (lev a).left
    rw [Category.assoc, hlev', reassoc_of% e]
  have σlev : ∀ a, σ (toUnit _ ≫ lev a) = toUnit _ ≫ c.lev a := fun a => (hσ _ _).2 (pt a)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    refine (_root_.GlobalTheory.weilIs_fieldExt_iff _ A₀ k Ω j' (spMap i') _ _ _ _ _ ab hD).1 ?_
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A (spMap i) φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    rw [map_zpow]
    exact weilIs_congr e.symm _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _ =>
    obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l B B' b b' S S' s s' o o' f

end GlobalTheory
end

