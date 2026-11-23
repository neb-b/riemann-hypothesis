module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0198
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  first | exact @GlobalTheory.SystemAmple.exists_system_ampFrames | exact GlobalTheory.SystemAmple.exists_system_ampFrames | (intros; apply GlobalTheory.SystemAmple.exists_system_ampFrames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.GraphCut

abbrev graphLB {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (N : ℕ) : LB X :=
  LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]

theorem cls_graphLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : X ⟶ X) (N : ℕ) (h : (graphLB L f N).IsLB) :
    cls _ h = N • cls L hL + N • pull f (cls L hL) := by
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp [pull_id]

theorem unitS_spMap {o K : Type} [CommRing o] [CommRing K] (β : o →+* K) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  exact (congrArg (fun φ => φ.hom (u : o)) h).symm

theorem vol_inv (H1 : Out.Laws) (H2 : Out.Laws2) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 1 ≤ N) :
    SymB (graphLB P.L ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left N) ∧
      ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (graphLB P.L ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left N) e) ((N * 2) ^ P.g * e ^ P.g) := by
  have hi : ((𝟙 P.A)⁻¹ : P.A ⟶ P.A) = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [hi]
  have hs : cls P.L P.isLB = pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) :=
    (cls_eq_iff P.isLB (pull_isLB P.isLB _)).2 (_root_.GlobalTheory.principal_polarisation_numerics H1 H2 K P).2.2.1
  have hB : (graphLB P.L (GrpObj.inv : P.A ⟶ P.A).left N).IsLB := LB.isLB_linComb P.isLB _ _
  have hc := cls_graphLB P.isLB _ N hB
  rw [← hs] at hc
  refine ⟨(cls_eq_iff hB (pull_isLB hB _)).1 ?_, fun e he => ?_⟩
  · rw [cls_pull hB, hc, map_add (f := _), map_nsmul, ← hs]
  · have h0 : SectionsHaveFiniteDimension P.A.hom (lbPow P.L (N * 2 * e)) ((N * 2 * e) ^ P.g) :=
      GlobalTheory.PowSec.exists_basis_sections H1.globalSectionsRank K P (N * 2 * e) (Nat.succ_le_of_lt (by positivity))
    rw [← mul_pow]
    have h1 : (lbPow P.L (N * 2 * e)).IsLB := LB.isLB_linComb P.isLB _ _
    have h2 : (lbPow (graphLB P.L (GrpObj.inv : P.A ⟶ P.A).left N) e).IsLB := LB.isLB_linComb hB _ _
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ h1).2.1 _ h2 ((cls_eq_iff h1 h2).1 ?_)).1 _ h0
    rw [cls_lbPow P.isLB, cls_lbPow hB, hc, ← add_nsmul, smul_smul]
    congr 1
    ring

theorem exists_vol (H1 : Out.Laws) (H2 : Out.Laws2) (g : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (κ N l m k : ℕ) (hk : k = l ^ m) (hm : m ≠ 0) (hN : 1 ≤ N) (hl : l.Prime) (hlt : (N * (1 + κ)) ^ (2 * g) < k)
    (o : Type) [CommRing o] (b : TBase o k) (i : Option J) :
    ∃ δ ≤ (N * (2 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g k J b (spMap β))
      (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → TorsBasis t.A k t.pt →
      SymB (graphLB t.L f.left N) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension t.A.hom (lbPow (graphLB t.L f.left N) e) (δ * e ^ g) := by
  subst hk
  cases i with
  | none =>
    refine ⟨(N * 2) ^ g, Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _, ?_⟩
    intro K _ _ β t f _ hf _
    subst hf
    exact vol_inv H1 H2 K t.pol N hN
  | some i =>
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.T.hilbertFunction_endomorphismGraph_of_torsionAction H1 H2 g N κ l m ((Mat i).map (Int.cast : ℤ → ZMod (l ^ m))) hN hl hlt
    refine ⟨δ, hδ.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) _), ?_⟩
    intro K _ _ β t f hS hf hT
    subst hf
    have hl0 : (l : K) ≠ 0 := by
      have := (b.unit.map β).ne_zero
      rw [map_natCast, Nat.cast_pow] at this
      exact fun h => this (by rw [h, zero_pow hm])
    refine H K t.pol t.pt (Units.map β.toMonoidHom b.ζ) (t.act i) rfl hl0
      (IsPrimitiveRoot.coe_units_iff.1 (b.prim K β)) hT (fun a a' => ?_) (t.hom i) ⟨hT.pos, (hS i).1⟩ (hS i).2
    have := t.pairing a a'
    rw [unitS_spMap] at this
    have e : unitOn ((Units.map β.toMonoidHom b.ζ) ^ Out.stdSymp g a a') =
      unitOn (Units.map β.toMonoidHom b.ζ) ^ Out.stdSymp g a a' := map_zpow (Units.map _) _ _
    rw [e]
    exact this

theorem lift_left_eq {S : Scheme.{0}} {A : Over S} [IsIso (snd (Over.mk (𝟙 S)) A).left] (y : Over.mk (𝟙 S) ⟶ A) :
    y.left ≫ inv (snd (Over.mk (𝟙 S)) A).left = (lift (𝟙 (Over.mk (𝟙 S))) y).left := by
  rw [IsIso.comp_inv_eq, ← Over.comp_left, lift_snd]

theorem pow_comp_graph {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Option J) {T : Over S} (x : T ⟶ t.A) (m : ℕ) :
    (x ^ m) ≫ i.elim (𝟙 t.A)⁻¹ t.act = (x ≫ i.elim (𝟙 t.A)⁻¹ t.act) ^ m := by
  cases i with
  | none => simp only [Option.elim_none, GrpObj.comp_inv, Category.comp_id, inv_pow]
  | some i =>
    haveI := t.hom i
    exact MonObj.pow_comp x m (t.act i)

theorem cutBy_graphIdeal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (i : Option J), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p q : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) ∧ SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left (q h)) → CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2) := by
  intro H1 H2 g J _ Mat κ n hn hodd
  have hn2 : 2 ≤ n := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, Hc⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H1 H2 g ((n ^ 2) ^ 2 * (2 + κ)) (Ix g ((n ^ 2) ^ 2) × Ix g ((n ^ 2) ^ 2))
  refine ⟨2 + k₀ + ((n ^ 2) ^ 2 * (1 + κ)) ^ (2 * g), fun j hj o _ b i => ?_⟩
  have hjn : j < n ^ j := Nat.lt_pow_self hn2
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  obtain ⟨δ, hδ, Hv⟩ := exists_vol H1 H2 g J Mat κ ((n ^ 2) ^ 2) n (j * 2) ((n ^ j) ^ 2) (pow_mul n j 2).symm (by omega)
    (Nat.succ_le_of_lt (by positivity)) hn
    (lt_of_lt_of_le (lt_of_le_of_lt (by omega) hjn) (Nat.le_self_pow two_ne_zero _)) o b i
  let c : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ 2) ^ 2) := fun a u => ZMod.castHom hdvd2 (ZMod ((n ^ 2) ^ 2)) (a u)
  have hc : Function.Surjective c := fun a => by
    choose a' ha' using fun u => ZMod.castHom_surjective hdvd2 (a u)
    exact ⟨a', funext ha'⟩
  have hc' : ∀ a a', c a = c a' → ∀ u, (a u).val ≡ (a' u).val [MOD (n ^ 2) ^ 2] := fun a a' h u => by
    have := congrFun h u
    simp only [c, ZMod.castHom_apply, ZMod.cast_eq_val] at this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this
  obtain ⟨Q, HQ⟩ := Hc δ hδ (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Prod.map c c) (hc.prodMap hc)
  refine ⟨Q, d, fun K _ _ β t σ p q f hS hf hE hpq => ?_⟩
  obtain ⟨hiso, hLB, hVA, hpow, hper, hT, hsurj⟩ := _root_.GlobalTheory.embSec_veryAmple_periodic H1 H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (hn2.trans (Nat.le_self_pow two_ne_zero n)) hE
  obtain ⟨hsym, hH⟩ := Hv K β t f hS hf hT
  have ha₂ : (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left ≫ (fst (Over.mk (𝟙 (Sp K))) t.A).left =
      (fst (Over.mk (𝟙 (Sp K))) t.A).left := by rw [← Over.comp_left, lift_fst]
  have ha₂' : (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left =
      (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ f.left := by rw [← Over.comp_left, lift_snd, Over.comp_left]
  obtain ⟨M, th, hM, hMVA, hMiso, hid, hco, hMper⟩ := GlobalTheory.ZV.GraphSystem.exists_product_system K _ _ _ _ _ (fst (Over.mk (𝟙 (Sp K))) t.A).left _ _ _ _ σ σ
    (𝟙 _) (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left hLB hLB hVA hVA inferInstance (Category.id_comp _) ha₂
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    ((Over.w (snd (Over.mk (𝟙 (Sp K))) t.A)).trans (Over.w (fst (Over.mk (𝟙 (Sp K))) t.A)).symm).trans (Category.comp_id _)
  have hB : (graphLB t.L f.left ((n ^ 2) ^ 2)).IsLB := LB.isLB_linComb t.isLB _ _
  have hP : (lbPow t.L ((n ^ 2) ^ 2)).IsLB := LB.isLB_linComb t.isLB _ _
  have c₁ := (cls_eq_iff hLB (pull_isLB hP _)).2 hpow
  rw [cls_pull hP, cls_lbPow t.isLB] at c₁
  have c₂ := (cls_eq_iff (LB.isLB_div hM (pull_isLB hLB _)) (pull_isLB hLB _)).2 hMiso
  rw [cls_div hM (pull_isLB hLB _), cls_pull hLB, cls_pull hLB, pull_id, c₁, ← pull_comp, ha₂', pull_comp,
    sub_eq_iff_eq_add', ← map_add, map_nsmul, ← cls_graphLB t.isLB _ _ hB] at c₂
  have c₃ : cls (M.pull e.inv) (pull_isLB hM _) = cls _ hB := by
    rw [cls_pull hM, c₂, ← pull_comp]
    exact (congrArg (fun φ => pull φ (cls _ hB)) e.inv_hom_id).trans (pull_id _)
  rw [hid, ← he]
  refine HQ K t.pol rfl _ e M th (n ^ j) _ (fun h => t.lab h ^ n ^ j) _ hM ?_ (he ▸ hMVA) ?_ ?_ (by omega) ?_ hsurj ?_
  · refine (cls_eq_iff (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)).1 ?_
    rw [cls_pull (pull_isLB hM _)]
    exact c₃.trans (((cls_eq_iff hB (pull_isLB hB _)).2 hsym).trans (congrArg (pull (GrpObj.inv : t.A ⟶ t.A).left) c₃.symm))
  · intro a a' h
    exact hMper a a' (hper _ _ (hc' _ _ (congrArg Prod.fst h))) (hper _ _ (hc' _ _ (congrArg Prod.snd h)))
  · intro m hm
    have h1 : (lbPow (graphLB t.L f.left ((n ^ 2) ^ 2)) m).IsLB := LB.isLB_linComb hB _ _
    have h2 : (lbPow M m).IsLB := LB.isLB_linComb hM _ _
    have h3 := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ t.A.hom _ h1).2.2.2.2.2 _ e _).1 (hH m hm)
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ (pull_isLB h1 e.hom)).2.1 _ h2 ((cls_eq_iff (pull_isLB h1 _) h2).1 ?_)).1 _ h3
    rw [cls_pull h1, cls_lbPow hB, cls_lbPow hM, map_nsmul, c₂]
    rfl
  · have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow] at this
    exact fun h => this (by rw [h, zero_pow two_ne_zero])
  · intro h
    have hy : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := lift_left_eq _
    have hy' : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left ≫
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left =
        (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hf, pow_comp_graph]
    have := hco K (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) (q h)
      (by rw [Category.comp_id]; exact (hpq h).1) (by rw [hy']; exact (hpq h).2)
    rw [← hy] at this
    exact this

end GlobalTheory.GraphCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClauses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section Incl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H} {c : Coeff l}
  {c₂ : Coeff l₂} {W : ValuationSubring ℂ}

theorem exists_isIncl (hc : c.F ≤ c₂.F) : ∃ b : c.V W →+* c₂.V W, IsIncl b := by
  refine ⟨RingHom.codRestrict ((IntermediateField.inclusion hc).toRingHom.comp (c.V W).subtype) (c₂.V W)
    (fun x => x.2), fun x => rfl⟩

theorem isIncl_unique {b b' : c.V W →+* c₂.V W} (hb : IsIncl b) (hb' : IsIncl b') : b = b' := by
  refine RingHom.ext fun x => Subtype.ext (Subtype.ext ?_)
  exact (hb x).trans (hb' x).symm

end Incl

theorem system_clauses : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW, N2 (S.Y p W hp hW) := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hD hN S p W hp hW
  refine ⟨fun i => (GlobalTheory.T.localModel_oneModel_and_splitFibres hext L1 L2 L3 E H D Xo hD hN S p W hp hW i).1, ?_⟩
  obtain ⟨hnp, hodd, h3, h4⟩ := S.aux (S.ch p)
  have hcop := (_root_.GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level E H).2 _ (S.aux (S.ch p))
  obtain ⟨-, hl2, hl3⟩ := GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp
  have key : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F →
      ∃ π : (S.Y p W hp hW i₂).X ⟶ (S.Y p W hp hW i).X, ∀ b : i.c.V W →+* i₂.c.V W, IsIncl b →
        IsTransition (S.Y p W hp hW i) (S.Y p W hp hW i₂) b π := by
    intro i i₂ hl hc
    obtain ⟨b, hb⟩ := exists_isIncl (W := W) hc
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₂
    obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_transition_map_raised_models hext L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN l₀ l₀' _ _ i.l i.c _ _
      (S.Y p W hp hW i) i₂.l i₂.c _ _ (S.Y p W hp hW i₂) b hnp.pos ⟨_, dvd_rfl⟩ (hl3 _ _ _ _ h₀ h₀' hl)
      (hl2 _ _ h₀).1 (hl2 _ _ h₀').1 hl hc ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW).1
      ((GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i₂.l i₂.c).2.2.2 p W hp hW).1 hb hr hr'
    exact ⟨π, fun b' hb' => isIncl_unique hb hb' ▸ hπ⟩
  choose π hπ using key
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.cm_models_siegel_family_comparison L1 L2 L3 E H D Xo _ _ (S.T (S.ch p)) hN p hp (S.ch_ne p).symm hnp ⟨_, rfl⟩
  refine ⟨π, hπ, S.n (S.ch p), S.J (S.ch p), Ag, hnp, hodd, S.ch_ne p, ?_, hcop, ?_⟩
  · have h2 : 3 ≤ S.n (S.ch p) := by
      have := hnp.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    exact h2.trans (Nat.le_self_pow (by have := S.J_pos (S.ch p); omega) _)
  · intro i i₁ hl hc b z hb hz hM hMb hA hF
    obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
    obtain ⟨l₀', h₀', hr'⟩ := S.raises p W hp hW i₁
    have h₁ : IsPrimeToPart l₀' i.l p := by
      obtain ⟨a1, a2, a3⟩ := h₀'
      exact ⟨a1, hM ▸ a2, hMb ▸ a3⟩
    obtain rfl : l₀' = l₀ := (hl2 _ _ h₀).2.2 _ h₁
    exact hAg W l₀' _ i.l i₁.l i.c i₁.c _ _ b z _ hW h₀ (hcop _) hb hz hM hMb hA hF hr hr' (hπ i i₁ hl hc b hb)

end GlobalTheory.Models
end

