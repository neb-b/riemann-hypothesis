module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.adjoint_of :
    PairCalc → TorsFree → Adjoint := by
  intro hPC hTF p _ D R _ b N k _ s c o o' ψ ψ' hψ hψ' hc T x y
  have hpos : 0 < c := hψ.pos
  obtain ⟨a₁, a₂, -, -, hsim⟩ := hPC p D R b N _ s o
  obtain ⟨a₁', a₂', -, -, -⟩ := hPC p D R b N _ s o'
  obtain ⟨-, hmon, -, -, hiso, -⟩ := hψ
  have hsim' := (hsim o' ψ c).1 hiso
  haveI := hmon
  haveI := hψ'

  have hsym : ∀ (q : Obj b N s) {Y : Over (Sp k)} (u v : Y ⟶ q.A),
      evc q.isLB u v = evc q.isLB v u := by
    intro q Y u v
    have h1 := (GlobalTheory.CechPic.cls_eq_iff q.isLB (pull_isLB q.isLB _)).2 q.symm
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift u v).left) h1
    rw [GlobalTheory.AbDual.cls_ev q.isLB, GlobalTheory.AbDual.pull_evc, lift_snd, lift_fst] at h2
    exact h2

  have hL1 := pull_isLB o'.isLB (lift (fst o.A o'.A ≫ ψ) (snd o.A o'.A)).left
  have hL2 := pull_isLB o.isLB (lift (fst o.A o'.A) (snd o.A o'.A ≫ ψ')).left
  have hL := LB.isLB_div hL1 hL2
  have cL := GlobalTheory.CechPic.cls_div hL1 hL2 hL
  have hev : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc hL u v = evc o'.isLB (u ≫ ψ) v - evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [GlobalTheory.AbDual.evc, cL, map_sub, GlobalTheory.AbDual.cls_ev o'.isLB, GlobalTheory.AbDual.cls_ev o.isLB,
      GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc]
  have add₁ := (GlobalTheory.AbDual.isAdditive_iff o.isLB).1 a₁
  have add₁' := (GlobalTheory.AbDual.isAdditive_iff o'.isLB).1 a₁'
  have add₂ := (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 a₂
  have add₂' := (GlobalTheory.BirigidLift.isAdditive_swap_iff o'.isLB).1 a₂'
  have bL₁ : IsAdditive (A := o.A) (T := o'.A) _ := (GlobalTheory.AbDual.isAdditive_iff hL).2 fun Y u u' v ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₁', add₁]
    abel
  have bL₂ : IsAdditive (swap _) := (GlobalTheory.BirigidLift.isAdditive_swap_iff hL).2 fun Y u v v' ↦ by
    rw [hev, hev, hev, MonObj.mul_comp, add₂', add₂]
    abel

  have hpow : ∀ {Y : Over (Sp k)} (u : Y ⟶ o'.A) (v : Y ⟶ o'.A) (n : ℕ),
      evc o'.isLB u (v ^ n) = n • evc o'.isLB u v := by
    intro Y u v n
    induction n with
    | zero =>
      have e := add₂' Y u 1 1
      rw [_root_.mul_one] at e
      rw [pow_zero, zero_smul]
      exact left_eq_add.1 e
    | succ n ih => rw [pow_succ, add₂', ih, succ_nsmul]
  have hcm : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      c • evc o'.isLB (u ≫ ψ) v = c • evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← hsim' Y u (v ≫ ψ'), ← hpow, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
  have hcls : GlobalTheory.CechPic.cls _ hL = evc hL (fst o.A o'.A) (snd o.A o'.A) := by
    rw [GlobalTheory.AbDual.evc, lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have hz : GlobalTheory.CechPic.cls _ hL = 0 := hTF k o.A o'.A o.ab o'.ab _ hL bL₁ bL₂ c hpos (by
    rw [hcls, hev, smul_sub, hcm, sub_self])
  have hmain : ∀ {Y : Over (Sp k)} (u : Y ⟶ o.A) (v : Y ⟶ o'.A),
      evc o'.isLB (u ≫ ψ) v = evc o.isLB u (v ≫ ψ') := by
    intro Y u v
    rw [← sub_eq_zero, ← hev, GlobalTheory.AbDual.evc, hz, map_zero]
  exact ⟨hmain x y, by rw [hsym o', hmain, hsym o]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobIsog
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isIso_spMap_pow {K : Type} [Field K] [IsAlgClosed K] (φ : K →+* K) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ a, φ a = a ^ n) : IsIso (spMap φ) := by
  have hbij : Function.Bijective φ := by
    refine ⟨φ.injective, fun x => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x hn
    exact ⟨z, by rw [hφ, hz]⟩
  haveI : IsIso (CommRingCat.ofHom φ) := (RingEquiv.ofBijective φ hbij).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

private theorem cls_hecke_pow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  apply (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans
  simp [GlobalTheory.CechPic.pull_id]

private theorem square_map_fst_left {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (g : A ⟶ B) : sq2 g ≫ (fst B B).left = (fst A A).left ≫ g.left := by
  simp only [sq2, ← Over.comp_left, lift_fst]

private theorem square_map_snd_left {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (g : A ⟶ B) : sq2 g ≫ (snd B B).left = (snd A A).left ≫ g.left := by
  simp only [sq2, ← Over.comp_left, lift_snd]

private theorem tensor_left_ext {S X : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (u v : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have hw : u ≫ (A ⊗ A).hom = v ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, h₁, Category.assoc]
  have key : (Over.homMk u rfl : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A) = Over.homMk v hw.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa using h₁
    · ext
      simpa using h₂
  simpa using congrArg CommaMorphism.left key

theorem UpperTheory.Gal.crystallineComparison.Mod.frobIsog_of :
    FrobHom → FrobFin → PicFrob → QuasiInv → FrobIsog := by
  intro hHom hFin hPic hQI p _ D R _ b N f κ _ _ _ s φ hφ hs o
  have hp : Nat.Prime p := Fact.out
  have hκ := GlobalTheory.SS.FrobField.cast_zero_sp κ (p := p) (CharP.cast_eq_zero κ p)
  obtain ⟨o₁, ⟨m₁⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp κ) (Sp κ) s (spMap φ) o
  revert o₁ m₁
  rw [hs]
  intro o₁ m₁
  have hA := GlobalTheory.SS.FrobField.cast_zero_of_hom o.A.hom hκ
  obtain ⟨F, hFm, hFφ, hFk⟩ := hHom p f hp κ φ hφ o.A o₁.A m₁.φ m₁.cart hA
  have hn : 0 < p ^ f := pow_pos hp.pos f
  haveI : IsIso (spMap φ) := isIso_spMap_pow φ hn hφ
  haveI : IsIso m₁.φ := m₁.cart.1.isIso_fst_of_isIso
  have hFsp : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hFφ' : ∀ {Z : Scheme} (h : o.A.left ⟶ Z),
      Over.Hom.left F ≫ m₁.φ ≫ h = GlobalTheory.SS.FrobField.absFrob o.A.left p f hp hA ≫ h := by
    intro Z h
    rw [← Category.assoc, hFφ]
  have hpt : ∀ (a : 𝟙_ (Over (Sp κ)) ⟶ o.A),
      Over.Hom.left a ≫ Over.Hom.left F ≫ m₁.φ = spMap φ ≫ Over.Hom.left a := by
    intro a
    rw [hFφ, ← GlobalTheory.SS.FrobField.absFrob_nat (Over.Hom.left a) p f hp hκ hA]
    exact congrArg (· ≫ Over.Hom.left a) hFsp
  have hact : ∀ c, o.act.act c ≫ F = F ≫ o₁.act.act c := by
    intro c
    ext1
    rw [← cancel_mono m₁.φ]
    simp only [Over.comp_left, Category.assoc, m₁.act, hFφ, hFφ']
    exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hA hA).symm
  have heta : ∀ x, o₁.eta x = o.eta x ≫ F := by
    intro x
    ext1
    rw [← cancel_mono m₁.φ, m₁.eta, Over.comp_left, Category.assoc, hpt]
  have hG := GlobalTheory.SS.FrobField.cast_zero_of_hom (G2 o.A).hom hκ
  have hsq : sq2 F ≫ m₁.φ₂ = GlobalTheory.SS.FrobField.absFrob (G2 o.A).left p f hp hG := by
    apply tensor_left_ext
    · rw [Category.assoc, m₁.sq.1, ← Category.assoc, square_map_fst_left, Category.assoc, hFφ]
      exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hG hA).symm
    · rw [Category.assoc, m₁.sq.2, ← Category.assoc, square_map_snd_left, Category.assoc, hFφ]
      exact (GlobalTheory.SS.FrobField.absFrob_nat _ p f hp hG hA).symm
  have hpol : Nonempty (LBIso (Hecke.lbPow o.P (p ^ f)) (o₁.P.pull (sq2 F))) := by
    have h1 : (Hecke.lbPow o.P (p ^ f)).IsLB :=
      LB.isLB_linComb o.isLB (fun _ : Fin (p ^ f) => 𝟙 _) (fun _ => (1 : ℤ))
    have h2 := pull_isLB o₁.isLB (sq2 F)
    have h3 := pull_isLB o.isLB m₁.φ₂
    have e1 : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m₁.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) := by
      rw [(GlobalTheory.CechPic.cls_eq_iff o₁.isLB h3).mpr m₁.pol, GlobalTheory.CechPic.cls_pull]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff h1 h2).mp ?_⟩
    rw [cls_hecke_pow o.isLB, GlobalTheory.CechPic.cls_pull o₁.isLB, e1, ← GlobalTheory.CechPic.pull_comp, hsq, hPic]
  have hFl : Over.Hom.left F = GlobalTheory.SS.FrobField.absFrob o.A.left p f hp hA ≫ inv m₁.φ := by
    rw [← hFφ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hlft : LocallyOfFiniteType o.A.hom := by
    haveI := o.ab
    haveI : Smooth o.A.hom := IsAbelianScheme.smooth
    infer_instance
  obtain ⟨hfin, hsurj⟩ := hFin p f hp κ o.A.left o.A.hom hlft hA
  have hfin' : IsFinite (Over.Hom.left F) := by
    rw [hFl]
    infer_instance
  have hsurj' : Surjective (Over.Hom.left F) := by
    rw [hFl]
    infer_instance
  have hker : ∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp κ) (g : Over.mk z ⟶ o.A),
      g ≫ F = 1 → g = 1 := by
    intro K _ _ z g hg
    have hT := GlobalTheory.SS.FrobField.cast_zero_of_hom z hκ
    haveI : CharP K p := charP_of_injective_ringHom (Spec.preimage z).hom.injective p
    haveI : ExpChar K p := ExpChar.prime hp
    have hτ : ∀ c : K, iterateFrobenius K p f c = c ^ p ^ f := by
      intro c
      simp [iterateFrobenius_def]
    haveI : IsIso (spMap (iterateFrobenius K p f)) := isIso_spMap_pow _ hn hτ
    have hFK : GlobalTheory.SS.FrobField.absFrob (Over.mk z).left p f hp hT = spMap (iterateFrobenius K p f) :=
      GlobalTheory.SS.FrobField.absFrob_spec K p f hp hT _ hτ
    have hk := (hFk _ g).mp hg hT
    rw [hFK, cancel_epi] at hk
    exact Over.OverMorphism.ext hk
  obtain ⟨ψ', hψm, e1, e2⟩ := hQI p D R b N κ s (p ^ f) hn o o₁ F hFm hfin' hsurj' hpol hker
  refine ⟨o₁, m₁, F, ⟨⟨f, rfl⟩, hFm, hact, heta, hpol, ψ', hψm, e1, e2⟩, ?_, hFk⟩
  intro a
  rw [Over.comp_left, Category.assoc]
  exact hpt a
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobPass
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable def frPt {κ Λ Λ' : Type} [Field κ] [CommRing Λ] [CommRing Λ'] [Algebra κ Λ] [Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ') : algPt κ Λ' ⟶ algPt κ Λ :=
  Over.homMk (spMap σ) (by
    change spMap σ ≫ spMap (algebraMap κ Λ) = spMap (algebraMap κ Λ')
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ])

private theorem frob_mid (hI : InfE) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {r : ℤ} {κ : Type} [Field κ] {s : Sp κ ⟶ Sp R} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} {d : ℕ}
    (hrep : RepAlg o.A (UKer r o ψ) d)
    (hcard : Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [IsLocalRing Λ'] [Algebra κ Λ] [algΛ' : Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ')
    (ε : Λ →ₐ[κ] κ) (ε' : Λ' →+* κ) (h1 : ∀ c, ε' (algebraMap κ Λ' c) = c)
    (h2 : ε'.comp σ = ε.toRingHom) (g : algPt κ Λ ⟶ o.A)
    (hK : ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) (hinf : Inf ε g)
    (hker : spMap σ ≫ (g ≫ ψ).left = spMap σ ≫ (1 : algPt κ Λ ⟶ o'.A).left) :
    spMap σ ≫ g.left = spMap σ ≫ (1 : algPt κ Λ ⟶ o.A).left := by
  let ε'' : Λ' →ₐ[κ] κ := { ε' with commutes' := h1 }
  have hfl : (frPt σ hσ).left = spMap σ := rfl
  have hone : ∀ {X Y A : Over (Sp κ)} [GrpObj A] (f : X ⟶ Y), f ≫ (1 : Y ⟶ A) = 1 := by
    intro X Y A _ f
    simp [Hom.one_def]
  have hcomp : spMap ε''.toRingHom ≫ spMap σ = spMap ε.toRingHom := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h2]
  have hgψ : (frPt σ hσ ≫ g) ≫ ψ = 1 := by
    rw [← hone (frPt σ hσ)]
    ext1
    simp only [Over.comp_left] at hker ⊢
    rw [hfl, Category.assoc]
    exact hker
  obtain ⟨e, he⟩ := hK
  have hP : UKer r o ψ (algPt κ Λ') (frPt σ hσ ≫ g) := by
    refine ⟨hgψ, e, ?_⟩
    intro a ha
    rw [Category.assoc, he a ha, hone]
  have hinf' : Inf ε'' (frPt σ hσ ≫ g) := by
    unfold Inf at hinf ⊢
    rw [Over.comp_left, hfl, ← Category.assoc, hcomp]
    exact hinf
  have h0 := hI κ o.A (UKer r o ψ) d hrep hcard Λ' ε'' (frPt σ hσ ≫ g) hP hinf'
  have h0' := congrArg Over.Hom.left (h0.trans (hone (frPt σ hσ)).symm)
  simp only [Over.comp_left] at h0'
  exact h0'

theorem UpperTheory.Gal.crystallineComparison.Mod.frobPass_of :
    InfE → FrobPass := by
  intro hI p _ D R _ b N r f κ _ _ _ s o o' ψ hψ d hrep hcard
  haveI := hψ
  have hp : Nat.Prime p := Fact.out
  have hone' : ∀ {X A B : Over (Sp κ)} [GrpObj A] [GrpObj B] (h : A ⟶ B) [IsMonHom h], (1 : X ⟶ A) ≫ h = 1 := by
    intro X A B _ _ h _
    simp [Hom.one_def]
  let φ : κ ≃+* κ := iterateFrobeniusEquiv κ p f
  have hφ : ∀ c : κ, φ c = c ^ p ^ f := fun c => rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    have h0 := GlobalTheory.SS.FrobField.cast_zero_sp κ (CharP.cast_eq_zero κ p)
    have e := GlobalTheory.SS.FrobField.absFrob_spec κ p f hp h0 φ.toRingHom hφ
    have hk : spMap φ.toRingHom ≫ g.left = spMap φ.toRingHom ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
      rw [← e]
      exact hg h0
    have hinv : spMap φ.symm.toRingHom ≫ spMap φ.toRingHom = 𝟙 _ := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      simp
    ext1
    calc g.left = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ g.left := by rw [hinv, Category.id_comp]
      _ = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
        rw [Category.assoc, hk, ← Category.assoc]
      _ = _ := by rw [hinv, Category.id_comp]
  · intro Λ _ _ _ ε g hK hinf
    have hΛ : (p : Λ) = 0 := by
      rw [← map_natCast (algebraMap κ Λ), CharP.cast_eq_zero, map_zero]
    let τ := GlobalTheory.SS.FrobField.powHom Λ p f hp hΛ
    have hτ : ∀ c : Λ, τ c = c ^ p ^ f := fun c => rfl
    let ε' : Λ →+* κ := φ.symm.toRingHom.comp ε.toRingHom
    have h2 : ε'.comp τ = ε.toRingHom := by
      ext x
      show φ.symm (ε (x ^ p ^ f)) = ε x
      rw [map_pow, ← hφ, RingEquiv.symm_apply_apply]
    constructor
    · intro hk h
      have e := GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h τ hτ
      have hker : spMap τ ≫ (g ≫ ψ).left = spMap τ ≫ (1 : algPt κ Λ ⟶ o'.A).left := by
        rw [← e]
        exact hk h
      have h1 : ∀ c : κ, ε' (@algebraMap κ Λ _ _ (τ.comp (algebraMap κ Λ)).toAlgebra c) = c := by
        intro c
        show (ε'.comp τ) (algebraMap κ Λ c) = c
        rw [h2]
        exact ε.commutes c
      have := frob_mid hI hrep hcard (Λ' := Λ) (algΛ' := (τ.comp (algebraMap κ Λ)).toAlgebra) τ rfl ε ε' h1 h2 g
        ⟨hK.choose, hK.choose_spec⟩ hinf hker
      rw [← e] at this
      exact this
    · intro hk h
      have h' := hk h
      rw [Over.comp_left, ← Category.assoc, h', Category.assoc, ← Over.comp_left, hone']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsogComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem comp_pow' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : f ≫ (g ^ n) = (f ≫ g) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y) (toUnit X)]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem pow_comp' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Y] [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom g] (n : ℕ) : (f ^ n) ≫ g = (f ≫ g) ^ n := by
  exact map_pow (IsMonHom.monoidHom g X) f n

theorem UpperTheory.Gal.crystallineComparison.Mod.isogComp_of :
    PairCalc → IsogComp := by
  intro hP p _ D R _ b N S s c c' o o₁ o₂ ψ χ h1 h2
  obtain ⟨⟨k, rfl⟩, hψ, ha, he, hL, ψ', hψ', hψ1, hψ2⟩ := h1
  obtain ⟨⟨k', rfl⟩, hχ, ha', he', hL', χ', hχ', hχ1, hχ2⟩ := h2
  haveI := hψ
  haveI := hχ
  haveI := hψ'
  haveI := hχ'
  refine ⟨⟨k + k', (pow_add p k k').symm⟩, inferInstance, ?_, ?_, ?_, ⟨χ' ≫ ψ', inferInstance, ?_, ?_⟩⟩
  · intro a
    rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc]
  · intro x
    rw [he', he, Category.assoc]
  · rw [(hP p D R b N S s o).2.2.2.2 o₂ (ψ ≫ χ) (p ^ k * p ^ k')]
    intro T x y
    have e1 := ((hP p D R b N S s o).2.2.2.2 o₁ ψ (p ^ k)).1 hL
    have e2 := ((hP p D R b N S s o₁).2.2.2.2 o₂ χ (p ^ k')).1 hL'
    rw [← Category.assoc, ← Category.assoc, e2, e1, mul_comm, mul_smul]
  · rw [Category.assoc, ← Category.assoc χ, hχ1, pow_comp', Category.id_comp, comp_pow', hψ1,
      ← pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ', hψ2, pow_comp', Category.id_comp, comp_pow', hχ2,
      ← pow_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem pt_core {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s} {o₁ o₁' : Obj b N s'}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A)
    (hsq : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (T : Over S') (g : T ⟶ o₁.A) :
    (g ≫ ψ₁ = 1 ↔ m.ptEquiv T g ≫ ψ = 1) ∧ (g = 1 ↔ m.ptEquiv T g = 1) ∧
      ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I (m.ptEquiv T g) := by
  have key : m'.ptEquiv T (g ≫ ψ₁) = m.ptEquiv T g ≫ ψ := by
    apply Over.OverMorphism.ext
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, ← hsq,
      Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key, MulEquiv.map_eq_one_iff]
  · rw [MulEquiv.map_eq_one_iff]
  · intro I
    unfold KilledBy
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]

theorem UpperTheory.Gal.crystallineComparison.Mod.pullKer_of :
    PullKer := by
  intro p _ D R _ b N S S' s s' f o o' o₁ o₁' m m' ψ ψ₁ hsq
  refine ⟨?_, ?_⟩
  · intro T T₀ h g g₀ hg₀
    have hw : T₀.hom = eqToHom h ≫ T.hom ≫ f := by
      have e1 := Over.w g₀
      have e2 := Over.w (m.ptEquiv T g)
      rw [ObjMap.ptEquiv_left] at e2
      simp only [Category.assoc] at e2
      rw [← e1, hg₀]
      simp only [Category.assoc]
      rw [e2]
      rfl
    obtain ⟨L, ⟨⟨⟩⟩, hom⟩ := T₀
    change L = T.left at h
    subst h
    simp only [eqToHom_refl, Category.id_comp] at hw hg₀
    subst hw
    have hg : g₀ = m.ptEquiv T g := by
      apply Over.OverMorphism.ext
      rw [ObjMap.ptEquiv_left, hg₀]
    subst hg
    exact pt_core m m' ψ ψ₁ hsq T g
  · intro r w j htj k _ _ _ x
    obtain ⟨h1, h2⟩ := htj k (x ≫ f)
    have c := fun g => pt_core m m' ψ ψ₁ hsq (Over.mk x) g
    refine ⟨fun g hg he => ?_, ?_⟩
    · rw [(c g).2.2 w]
      obtain ⟨n, hn⟩ := he
      exact h1 _ ((c g).1.mp hg) ⟨n, ((c g).2.2 _).mp hn⟩
    · rw [← h2]
      exact Nat.card_congr ((m.ptEquiv (Over.mk x)).toEquiv.subtypeEquiv fun g => by
        rw [(c g).1, (c g).2.2 w]
        rfl)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledEx_of :
    ObjTri → PullIsog → PullKer → PulledEx := by
  intro hTri hIsog hKer p _ D R _ b N hN hc M r w j c T S x σ hx o₁ m₁ y hy
  obtain ⟨m₀, htri⟩ := (hTri p D R b N hN hc S T.Y M.X σ (T.s ≫ M.s) M.s o₁ T.o M.univ y T.s).2 x hy m₁ T.ms
  have hσ : y ≫ T.s ≫ M.s = σ := by rw [← Category.assoc, hy, hx]
  obtain ⟨o', m', ψ, hisog, hsq⟩ := hIsog p D R b N T.Y S (T.s ≫ M.s) σ y hσ c T.o T.o' T.ψ T.isog o₁ m₀
  have htj := (hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ o' m₀ m' T.ψ ψ hsq).2 r w j T.tj
  exact ⟨⟨o', ψ, m₀, m', hsq, htri, hisog, htj⟩⟩
end

