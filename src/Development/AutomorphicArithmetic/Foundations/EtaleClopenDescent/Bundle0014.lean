module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsObjMapOfPIsogenyPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  intro p _ D R _ b N c T Y s₁ s t o₁ o₁' o o' m ψ₁ ψ θ hp hψ₁ hψ hcart hmc
  obtain ⟨θ₂, hθ₂1, hθ₂2⟩ : ∃ θ₂ : (G2 o₁'.A).left ⟶ (G2 o'.A).left,
      θ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ θ ∧
      θ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ θ := by
    refine ⟨Limits.pullback.lift (Limits.pullback.fst _ _ ≫ θ) (Limits.pullback.snd _ _ ≫ θ) ?_,
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
    rw [Category.assoc, Category.assoc, hcart.1.w, ← Category.assoc, ← Category.assoc,
      Limits.pullback.condition]
  have ext2 : ∀ {Z : Scheme} (f g : Z ⟶ (G2 o'.A).left),
      f ≫ (fst o'.A o'.A).left = g ≫ (fst o'.A o'.A).left →
      f ≫ (snd o'.A o'.A).left = g ≫ (snd o'.A o'.A).left → f = g :=
    fun f g h1 h2 => Limits.pullback.hom_ext h1 h2
  obtain ⟨ψ₁', hq⟩ := hψ₁.exists_quasiInv
  have hc : 0 < c := hψ₁.pos
  haveI := (SiegUniqBase.flat_surjective_qc_pow T o₁'.A o₁'.ab c hc).1
  haveI := (SiegUniqBase.flat_surjective_qc_pow T o₁'.A o₁'.ab c hc).2.1
  have hepi : Epi (Over.Hom.left (𝟙 o₁'.A ^ c)) := Flat.epi_of_flat_of_surjective _
  have he : Over.Hom.left (𝟙 o₁'.A ^ c) = ψ₁'.left ≫ ψ₁.left := by
    rw [← hq.2.2.2, Over.comp_left]
  have hone : (1 : o₁'.A ⟶ o₁'.A).left ≫ θ = θ ≫ (1 : o'.A ⟶ o'.A).left := by
    have h := GlobalTheory.LocTrivDescent.one_left_comp hcart
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at h
    rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
    rw [Category.assoc, ← Category.assoc θ, hcart.1.w, Category.assoc]
    congr 1
  have hs2 : ∀ {S : Scheme} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
      (f : A ⟶ A'), sq2 f ≫ (fst A' A').left = (fst A A).left ≫ f.left ∧
        sq2 f ≫ (snd A' A').left = (snd A A).left ≫ f.left := by
    intro S A A' _ _ _ _ f
    constructor <;> (rw [sq2, ← Over.comp_left]; simp)
  have hsq : sq2 ψ₁ ≫ θ₂ = m.φ₂ ≫ sq2 ψ := by
    apply ext2
    · simp only [Category.assoc]
      rw [hθ₂1, (hs2 ψ).1, ← Category.assoc (sq2 ψ₁), (hs2 ψ₁).1, ← Category.assoc m.φ₂, m.sq.1]
      simp only [Category.assoc, hmc]
    · simp only [Category.assoc]
      rw [hθ₂2, (hs2 ψ).2, ← Category.assoc (sq2 ψ₁), (hs2 ψ₁).2, ← Category.assoc m.φ₂, m.sq.2]
      simp only [Category.assoc, hmc]
  have hQ : (o'.P.pull θ₂).IsLB := pull_isLB o'.isLB θ₂
  have hcu : IsUnit ((c : ℕ) : Γ(T, ⊤)) := by
    obtain ⟨kk, rfl⟩ := hψ₁.exists_eq_pow
    rw [Nat.cast_pow]
    refine IsUnit.pow _ ?_
    have := hp.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s₁.appTop).hom
    simpa using this
  have hone2 : (lift 1 (𝟙 o₁'.A)).left ≫ θ₂ = θ ≫ (lift 1 (𝟙 o'.A)).left := by
    apply ext2
    · rw [Category.assoc, hθ₂1, ← Category.assoc, ← Over.comp_left, lift_fst, hone, Category.assoc, ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hθ₂2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp, Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id]
  have hone3 : (lift (𝟙 o₁'.A) 1).left ≫ θ₂ = θ ≫ (lift (𝟙 o'.A) 1).left := by
    apply ext2
    · rw [Category.assoc, hθ₂1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp, Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [Category.assoc, hθ₂2, ← Category.assoc, ← Over.comp_left, lift_snd, hone, Category.assoc, ← Over.comp_left, lift_snd]
  have r1 : ∃ t : ((o'.P.pull θ₂).pull (lift 1 (𝟙 o₁'.A)).left).Gen, t.IsGen := by
    rw [GlobalTheory.LocTrivDescent.triv_iff hQ, GlobalTheory.CechPic.cls_pull o'.isLB θ₂ hQ, ← GlobalTheory.CechPic.pull_comp,
      hone2, GlobalTheory.CechPic.pull_comp, (GlobalTheory.LocTrivDescent.triv_iff o'.isLB _).1 o'.rig₁, map_zero]
  have r2 : ∃ t : ((o'.P.pull θ₂).pull (lift (𝟙 o₁'.A) 1).left).Gen, t.IsGen := by
    rw [GlobalTheory.LocTrivDescent.triv_iff hQ, GlobalTheory.CechPic.cls_pull o'.isLB θ₂ hQ, ← GlobalTheory.CechPic.pull_comp,
      hone3, GlobalTheory.CechPic.pull_comp, (GlobalTheory.LocTrivDescent.triv_iff o'.isLB _).1 o'.rig₂, map_zero]
  have hiso : LBIso (o₁'.P.pull (sq2 ψ₁)) ((o'.P.pull θ₂).pull (sq2 ψ₁)) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₁'.isLB _) (pull_isLB hQ _)]
    obtain ⟨hI⟩ := hψ₁.2.2.2.2.1
    obtain ⟨hI'⟩ := hψ.2.2.2.2.1
    have e1 : c • GlobalTheory.CechPic.cls o₁.P o₁.isLB =
        GlobalTheory.CechPic.cls (o₁'.P.pull (sq2 ψ₁)) (pull_isLB o₁'.isLB _) := by
      rw [← GlobalTheory.LocTrivDescent.cls_lbPow_eq o₁.isLB c (LB.isLB_linComb o₁.isLB _ _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hI
    have e2 : c • GlobalTheory.CechPic.cls o.P o.isLB =
        GlobalTheory.CechPic.cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB _) := by
      rw [← GlobalTheory.LocTrivDescent.cls_lbPow_eq o.isLB c (LB.isLB_linComb o.isLB _ _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hI'
    have e3 := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    rw [← e1, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull o'.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _), ← e2,
      map_nsmul, ← GlobalTheory.CechPic.cls_pull o.isLB _ (pull_isLB o.isLB _), ← e3]
  refine ⟨⟨θ, θ₂, hcart, ⟨hθ₂1, hθ₂2⟩, ?_, ?_, ?_⟩, rfl⟩
  · intro c'
    rw [← cancel_epi (Over.Hom.left (𝟙 o₁'.A ^ c)), he]
    have h1 := congrArg Over.Hom.left (hψ₁.2.2.1 c')
    have h2 := congrArg Over.Hom.left (hψ.2.2.1 c')
    simp only [Over.comp_left] at h1 h2
    simp only [Category.assoc]
    rw [← reassoc_of% h1, ← hmc, reassoc_of% (m.act c'), h2, reassoc_of% hmc]
  · exact GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes T o₁.A o₁'.A c ψ₁ ψ₁' o₁'.P (o'.P.pull θ₂) o₁'.ab hc hcu
      hq (isAxesTriv_obj o₁') ⟨hQ, r1, r2⟩ hiso
  · intro y
    rw [hψ₁.2.2.2.1 y, Over.comp_left, Category.assoc, ← hmc, ← Category.assoc, m.eta y,
      Category.assoc, ← Over.comp_left, ← hψ.2.2.2.1 y]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPolarizationDescentOfQuasiIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hce hB hq hker
  obtain ⟨e, rfl⟩ := hce
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  haveI := hψ
  haveI := hψ'
  have hc0 : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hP := o.isLB
  have hlb : ∀ m, (Hecke.lbPow o.P m).IsLB := fun m => by
    unfold Hecke.lbPow
    exact LB.isLB_linComb hP _ _
  obtain ⟨Dd, _, Q, h, hD, hdual, hadd, hh, hiso⟩ :=
    GlobalTheory.T.exists_dual_abelian_scheme Y B o.A ψ' o.P hB o.ab hψ' hP o.rig₁ o.rig₂
  have hQ := hdual.isLB
  have etens : (ψ' ⊗ₘ ψ') = lift (fst B B ≫ ψ') (snd B B ≫ ψ') := by
    ext <;> simp
  have esq : Hecke.sq2 ψ' = Over.Hom.left (ψ' ⊗ₘ ψ') := by
    rw [etens]
    rfl
  have kiso := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hQ _)).2 hiso
  rw [GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull hQ] at kiso
  have hkerh : ∀ (T : Over Y) (σ : T.left ⟶ Y), σ ≫ 𝟙 Y = T.hom →
      ∀ a : T ⟶ B, a ^ (p ^ e) = 1 → a ≫ h = 1 := by
    intro T σ hσ a ha
    have ha3 : a ^ (p ^ e) ^ 3 = 1 := by
      rw [show (p ^ e) ^ 3 = p ^ e * (p ^ e) ^ 2 by ring, pow_mul, ha, one_pow]
    have htriv := (hker T σ hσ a ha3).2 ha
    apply hdual.eq_one
    have e1 : lift (fst B T) (snd B T ≫ a ≫ h) =
        lift (fst B T) (snd B T ≫ a) ≫ lift (fst B B) (snd B B ≫ h) := by
      ext <;> simp
    have e2 : lift (fst B T ≫ ψ') (snd B T ≫ a ≫ ψ') =
        lift (fst B T) (snd B T ≫ a) ≫ (ψ' ⊗ₘ ψ') := by
      rw [etens]
      ext <;> simp
    have k2 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 htriv
    rw [GlobalTheory.CechPic.cls_pull hP, e2, Over.comp_left, GlobalTheory.CechPic.pull_comp, kiso,
      ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, ← e1, ← GlobalTheory.CechPic.cls_pull hQ _ (pull_isLB hQ _)] at k2
    exact (GlobalTheory.CechPic.cls_eq_zero_iff _).1 k2
  have hunit : IsUnit (((p ^ e : ℕ) : Γ(Y, ⊤))) := by
    have h0 : IsUnit ((p : ℕ) : Γ(Sp R, ⊤)) := by
      have := hp.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this
    have h3 := h0.map s.appTop.hom
    rw [map_natCast] at h3
    simpa using h3.pow e
  obtain ⟨P', hP'lb, hr1, hr2, hP'iso⟩ :=
    GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle Y B Dd Q h (p ^ e) _ o.P (Over.Hom.left (ψ' ⊗ₘ ψ')) hB hD hdual hadd hh hc0 hunit hP
      hiso Y (𝟙 Y) B (𝟙 _) (𝟙 _) (GlobalTheory.SiegLower.isGrpPullback_id B) ⟨by simp, by simp⟩ hkerh
  have kP' := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (GlobalTheory.isLB_lbPow hP'lb _)).2 hP'iso
  rw [Category.id_comp, GlobalTheory.CechPic.cls_lbPow hP'lb, GlobalTheory.CechPic.cls_pull hP, ← esq] at kP'
  have hP2 : (P'.pull (Hecke.sq2 ψ)).IsLB := pull_isLB hP'lb _
  have sqc : Hecke.sq2 (ψ ≫ ψ') = Hecke.sq2 ψ ≫ Hecke.sq2 ψ' := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have eL1 : Over.Hom.left (lift (1 : o.A ⟶ o.A) (𝟙 o.A)) ≫ Hecke.sq2 ψ =
      Over.Hom.left ψ ≫ Over.Hom.left (lift (1 : B ⟶ B) (𝟙 B)) := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have eL2 : Over.Hom.left (lift (𝟙 o.A) (1 : o.A ⟶ o.A)) ≫ Hecke.sq2 ψ =
      Over.Hom.left ψ ≫ Over.Hom.left (lift (𝟙 B) (1 : B ⟶ B)) := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  refine ⟨P', ⟨hP'lb, hr1, hr2⟩, ?_, ?_⟩
  · rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (by unfold Hecke.lbPow; exact LB.isLB_linComb hP'lb _ _),
      GlobalTheory.BirigidPow.cls_lbPow hP'lb, GlobalTheory.CechPic.cls_pull hP, kP']
  · refine GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified Y o.A (p ^ e) _ _ o.ab hc0 hunit (hlb _) ?_ ?_ hP2 ?_ ?_ ?_
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (hlb _) _), GlobalTheory.CechPic.cls_pull (hlb _),
        GlobalTheory.BirigidPow.cls_lbPow hP, map_nsmul, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o.rig₁, nsmul_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (hlb _) _), GlobalTheory.CechPic.cls_pull (hlb _),
        GlobalTheory.BirigidPow.cls_lbPow hP, map_nsmul, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o.rig₂, nsmul_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _), GlobalTheory.CechPic.cls_pull hP2,
        GlobalTheory.CechPic.cls_pull hP'lb, ← GlobalTheory.CechPic.pull_comp, eL1, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ (pull_isLB hP'lb _), (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hr1, map_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _), GlobalTheory.CechPic.cls_pull hP2,
        GlobalTheory.CechPic.cls_pull hP'lb, ← GlobalTheory.CechPic.pull_comp, eL2, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ (pull_isLB hP'lb _), (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hr2, map_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_iff (GlobalTheory.isLB_lbPow (hlb _) _) (GlobalTheory.isLB_lbPow hP2 _),
        GlobalTheory.CechPic.cls_lbPow (hlb _), GlobalTheory.CechPic.cls_lbPow hP2, GlobalTheory.BirigidPow.cls_lbPow hP, smul_smul,
        ← pow_two, ← GlobalTheory.BirigidPow.cls_lbPow hP _ (hlb _),
        (GlobalTheory.CechPic.cls_eq_iff (hlb _) (pull_isLB hP _)).2
          (GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple Y o.A o.ab o.P hP o.rig₁ o.rig₂ o.ample (p ^ e)),
        ← h1, sqc, GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.pull_comp, kP', map_nsmul,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ hP2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationKernelOfPIsogenyQuasiInverse
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

open GlobalTheory.BirigidPow (val_one_left val_one_right val_pow_right comp_pow_pt) in
open GlobalTheory.CechPic (cls cls_pull cls_eq_iff cls_eq_zero_iff pull_comp) in
set_option maxHeartbeats 1000000 in
theorem UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  intro p _ D R _ b N c Y s o o' ψ ψ' hp hI hq T σ hσ x hx
  have hP := o.isLB
  have hP' := o'.isLB
  have hc0 : 0 < c := hI.pos
  obtain ⟨k, hk⟩ := hI.1
  haveI := hq.1
  haveI := hq.2.1
  have hu : IsUnit (c : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [hk, Nat.cast_pow]
    exact h.pow k

  have hQ1 : (o.P.pull (sq2 ψ')).IsLB := pull_isLB hP _
  have hQ2 : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb hP' _ _
  have cQ1 : cls _ hQ1 = GlobalTheory.CechPic.pull (sq2 ψ') (cls o.P hP) := cls_pull hP _ hQ1
  have cQ2 : cls _ hQ2 = c • cls o'.P hP' := GlobalTheory.BirigidPow.cls_lbPow hP' c hQ2
  have atQ₁ : ∀ {U : Over Y} (a b : U ⟶ o'.A),
      GlobalTheory.CechPic.pull (lift a b).left (cls _ hQ1) = GlobalTheory.BirigidPow.val hP (a ≫ ψ') (b ≫ ψ') := by
    intro U a b
    rw [cQ1, GlobalTheory.BirigidPow.val, ← pull_comp, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  have atQ₂ : ∀ {U : Over Y} (a b : U ⟶ o'.A),
      GlobalTheory.CechPic.pull (lift a b).left (cls _ hQ2) = c • GlobalTheory.BirigidPow.val hP' a b := by
    intro U a b
    rw [cQ2, map_nsmul, GlobalTheory.BirigidPow.val]
  have ax1 : IsAxesTriv o'.A (o.P.pull (sq2 ψ')) := by
    refine ⟨hQ1, (cls_eq_zero_iff (pull_isLB hQ1 _)).1 ?_, (cls_eq_zero_iff (pull_isLB hQ1 _)).1 ?_⟩
    · rw [cls_pull hQ1 _ (pull_isLB hQ1 _), atQ₁, MonObj.one_comp]
      exact val_one_left hP o.rig₁ _
    · rw [cls_pull hQ1 _ (pull_isLB hQ1 _), atQ₁, MonObj.one_comp]
      exact val_one_right hP o.rig₂ _
  have ax2 : IsAxesTriv o'.A (Hecke.lbPow o'.P c) := by
    refine ⟨hQ2, (cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_, (cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_⟩
    · rw [cls_pull hQ2 _ (pull_isLB hQ2 _), atQ₂, val_one_left hP' o'.rig₁, smul_zero]
    · rw [cls_pull hQ2 _ (pull_isLB hQ2 _), atQ₂, val_one_right hP' o'.rig₂, smul_zero]

  have eP : GlobalTheory.CechPic.pull (sq2 ψ) (cls o'.P hP') = c • cls o.P hP := by
    obtain ⟨i⟩ := hI.2.2.2.2.1
    have h := (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP' _)).2 i
    rw [cls_pull hP' _ (pull_isLB hP' _)] at h
    rw [← h]
    exact GlobalTheory.BirigidPow.cls_lbPow hP c _
  have eC : GlobalTheory.CechPic.pull (sq2 ((𝟙 o.A) ^ c)) (cls o.P hP) = (c ^ 2) • cls o.P hP := by
    have i := GlobalTheory.BirigidPow.lineBundleIso_tensorPowSq_pullback_mulPair hP o.ab o.ample o.rig₁ o.rig₂ c
    have h := (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP _)).2 i
    rw [cls_pull hP _ (pull_isLB hP _)] at h
    rw [← h]
    exact GlobalTheory.BirigidPow.cls_lbPow hP _ _
  have eS : sq2 ψ ≫ sq2 ψ' = sq2 ((𝟙 o.A) ^ c) := by
    rw [← hq.2.2.1, sq2, sq2, sq2, ← Over.comp_left, comp_lift]
    simp
  have iso : LBIso ((o.P.pull (sq2 ψ')).pull (sq2 ψ)) ((Hecke.lbPow o'.P c).pull (sq2 ψ)) := by
    refine (cls_eq_iff (pull_isLB hQ1 _) (pull_isLB hQ2 _)).1 ?_
    rw [cls_pull hQ1 _ (pull_isLB hQ1 _), cls_pull hQ2 _ (pull_isLB hQ2 _), cQ1, cQ2, map_nsmul, eP,
      ← pull_comp, eS, eC, smul_smul, sq]
  have cE : cls _ hQ1 = cls _ hQ2 := (cls_eq_iff hQ1 hQ2).2
    (GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A o'.A c ψ ψ' _ _ o'.ab hc0 hu hq ax1 ax2 iso)
  have key : ∀ {U : Over Y} (a b : U ⟶ o'.A), GlobalTheory.BirigidPow.val hP (a ≫ ψ') (b ≫ ψ') = c • GlobalTheory.BirigidPow.val hP' a b := by
    intro U a b
    rw [← atQ₁, cE, atQ₂]
  have hT : PullPolTriv o ψ' x ↔ GlobalTheory.BirigidPow.val hP' (fst o'.A T) (snd o'.A T ≫ x ^ c) = 0 := by
    unfold PullPolTriv
    rw [← cls_eq_zero_iff (pull_isLB hP _), cls_pull hP _ (pull_isLB hP _)]
    change GlobalTheory.BirigidPow.val hP _ _ = 0 ↔ _
    rw [← Category.assoc (snd o'.A T) x ψ', key, comp_pow_pt,
      val_pow_right hP' o'.ab o'.ample o'.rig₁ o'.rig₂]
  have hsym : ∀ {U : Over Y} (a b : U ⟶ o'.A), GlobalTheory.BirigidPow.val hP' a b = GlobalTheory.BirigidPow.val hP' b a := by
    intro U a b
    obtain ⟨i⟩ : Nonempty (LBIso o'.P (o'.P.pull (lift (snd o'.A o'.A) (fst o'.A o'.A)).left)) := ⟨o'.symm⟩
    have h := (cls_eq_iff hP' (pull_isLB hP' _)).2 i
    rw [cls_pull hP' _ (pull_isLB hP' _)] at h
    rw [GlobalTheory.BirigidPow.val, h, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst, GlobalTheory.BirigidPow.val]
  rw [hT]
  constructor
  · intro h
    obtain ⟨e, he, hker⟩ := o'.kerP
    have h1 : (x ^ c) ^ e = 1 := hker T (x ^ c)
      ((cls_eq_zero_iff (pull_isLB hP' _)).1 (by
        rw [cls_pull hP' _ (pull_isLB hP' _)]
        exact (hsym _ _).trans h))
    have h2 : (x ^ c) ^ (c ^ 2) = 1 := by
      rw [← pow_mul, ← pow_succ', hx]
    have hco : e.gcd (c ^ 2) = 1 := by
      rw [hk]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ he)
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hco, pow_one] at this
  · intro h
    rw [h, MonObj.comp_one]
    exact val_one_right hP' o'.rig₂ _
end

