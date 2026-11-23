module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEven
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TensPol

theorem rig_exists {R : Type} [CommRing R] [IsDomain R] {B : Over (Spec (CommRingCat.of R))} [GrpObj B] {M : LB B.left}
    (hM : M.IsLB) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {A' : Over (Spec (CommRingCat.of R))} [GrpObj A'] {L' : LB A'.left}
    (hL' : L'.IsLB) (pr : Fin r → (A' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : LB.Iso L' (LB.LinComb M (tensφ pr) (tensε W)))
    (hw : w.IsGen) : ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ B.left) → M.ι)
      (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good M z J → Good L' z J' →
      val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' *
        gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  have hform : FormEq (X := B.left) (Y := (𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (PEmpty.elim : PEmpty → _) PEmpty.elim
      (GlobalTheory.LamBiext.flatφ (tensφ pr) (fun _ : PUnit => eSec A'))
      (GlobalTheory.LamBiext.flatε (tensε W) (fun _ : PUnit => (1 : ℤ))) := by
    intro U _ h
    simp only [GlobalTheory.LamBiext.flatφ, GlobalTheory.LamBiext.flatε, GlobalTheory.Mum.TensRig.eSec_tensφ pr hpr, _root_.one_mul, Finset.univ_eq_empty,
      Finset.prod_empty, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε]
    simp
  obtain ⟨t, ht, htv⟩ := exists_gen hM hform (LB.oneGen M) (GlobalTheory.Mum.TensRig.oneGen_isGen' _)
  obtain ⟨a, ha, hmaps⟩ := Transport.exists_transport
    (DVR.linComb_isLB L' hL' (fun _ : PUnit => eSec A') (fun _ => 1))
    (DVR.linComb_isLB _ (DVR.linComb_isLB M hM (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A') (fun _ => 1))
    (LB.linCombIso w (fun _ : PUnit => eSec A') (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _)
    (GlobalTheory.LamBiext.nest M (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t)
    (GlobalTheory.LamBiext.nest_isGen ht)
  refine ⟨a, ha, fun z J J' hJ hJ' => ?_⟩
  have hPM := (GlobalTheory.GtCubeCompare.maps_iff_pm w (fun _ : PUnit => eSec A') (fun _ => 1) a _).1 hmaps
  have hp : (toUnit (TK R)).left z ∈ LB.wchart (LB.LinComb M (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (ptK η[A'] ≫ tensφ pr k)
  have hq : (toUnit (TK R)).left z ∈ LB.wchart L' (fun _ : PUnit => eSec A') (fun _ => J' (ptK η[A'])) :=
    Set.mem_iInter.2 fun _ => hJ' (ptK η[A'])
  have E := hPM _ (toUnit (TK R)).left z _ _ hp hq
  have L1 : gm (toUnit (TK R)).left z (LB.wchart (LB.LinComb M (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)))
      ((GlobalTheory.LamBiext.nest M (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t).s
        (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k))) = 1 := by
    refine (gm_res _ z (GlobalTheory.LamBiext.nest_le M (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') _) hp _).trans ?_
    exact (val_of t (toUnit (TK R)).left z J (fun p => J (ptK η[A'] ≫ tensφ pr p.2))
      (fun x => congrArg J (Category.assoc _ _ _).symm)).symm.trans ((htv _ _ z J hJ).trans (val_one _))
  rw [L1, Fintype.prod_unique, zpow_one] at E
  rw [val_pull hJ' a (toUnit (TK R)).left (𝟙 _),
    val_of a _ z J' (fun _ => J' (ptK η[A'])) (fun _ => by rw [Category.id_comp]; rfl), Category.id_comp, mul_comm]
  exact E.symm

end GlobalTheory.Mum.TensPol

noncomputable section
namespace GlobalTheory.Mum.TensPol

variable {R : Type} [CommRing R] [IsDomain R]

theorem formula_trans (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left}
    (pr : Fin r → (B' ⟶ Q.B)) {w : LB.Iso L' (LB.LinComb Q.M.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → Q.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ Q.c (y i)) (z : (TK R).left) (J J₀) (hJ : Good Q.M.L z J)
    (hJ₀ : Good Q.M.L z J₀) (k k₀ : L'.ι) (hk : x.left z ∈ L'.U k) (hk₀ : x.left z ∈ L'.U k₀) :
    gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) * ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z J ^ W i j =
      (gm x.left z _ (L'.g k k₀))⁻¹ * (gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) *
        ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z J₀ ^ W i j) := by
  let H : ((TK R).left ⟶ Q.B.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (Q.M.L.g (J ψ) (J₀ ψ))
  let F : Fin r → Fin r → ((TK R).left.presheaf.stalk z)ˣ := fun i j =>
    ∏ a, H (lamPts (toUnit (TK R) ≫ Q.c (y i)) (toUnit (TK R) ≫ Q.c (y j)) a) ^ Oε a
  have h₁ : gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) =
      gm x.left z _ ((LB.LinComb Q.M.L (tensφ pr) (tensε W)).g
        (fun a => J (x.left ≫ tensφ pr a)) (fun a => J₀ (x.left ≫ tensφ pr a))) *
      (gm x.left z _ (L'.g k k₀))⁻¹ *
      gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) := by
    let L := LB.LinComb Q.M.L (tensφ pr) (tensε W)
    let j := fun a => J (x.left ≫ tensφ pr a)
    let j₀ := fun a => J₀ (x.left ≫ tensφ pr a)
    have hj : x.left z ∈ L.U j := hJ.mem (tensφ pr) x.left
    have hj₀ : x.left z ∈ L.U j₀ := hJ₀.mem (tensφ pr) x.left
    have hV : x.left z ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) := ⟨⟨hj, hk⟩, ⟨hj₀, hk₀⟩⟩
    have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L.U j ⊓ L.U j₀) (L.g j j₀) *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L'.U k ⊓ L'.U k₀) (L'.g k k₀))⁻¹ *
        res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L.U j₀ ⊓ L'.U k₀) (w.s (j₀, k₀)) :=
      hw (j, k) (j₀, k₀)
    have key := congrArg (gm x.left z ((L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀))) hw' 
    simp only [map_mul, map_inv, gm_res x.left z _ hV] at key
    rw [gm_res x.left z (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
      gm_res x.left z (U := L.U j₀ ⊓ L'.U k₀) _ hV (w.s (j₀, k₀))] at key
    exact key
  have h₂ : gm x.left z _ ((LB.LinComb Q.M.L (tensφ pr) (tensε W)).g (fun a => J (x.left ≫ tensφ pr a))
      (fun a => J₀ (x.left ≫ tensφ pr a))) = ∏ i, ∏ j, F i j ^ W i j := by
    refine (gm_linComb Q.M.L (tensφ pr) (tensε W) x.left z _ _ (hJ.mem (tensφ pr) x.left) (hJ₀.mem (tensφ pr) x.left)).trans ?_
    change ∏ a, H (x.left ≫ tensφ pr a) ^ tensε W a = _
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [GlobalTheory.Mum.TraitWit.comp_tensφ, hx, hx, ← zpow_mul, mul_comm]
    rfl
  have h₃ : ∀ i j, val (Q.tau (y i) (y j)) (𝟙 _) z J = (F i j)⁻¹ * val (Q.tau (y i) (y j)) (𝟙 _) z J₀ := fun i j => by
    refine (gen_trans (Q.tau_gen (y i) (y j)) (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    change ∏ a, H (𝟙 _ ≫ lamPts (toUnit (TK R) ≫ Q.c (y i)) (toUnit (TK R) ≫ Q.c (y j)) a) ^ negε a = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Category.id_comp, ← zpow_neg]
    congr 1
    fin_cases a <;> rfl
  refine (congrArg₂ (· * ·) (h₁.trans (congrArg (· * _ * _) h₂)) (Finset.prod_congr rfl fun i _ =>
    Finset.prod_congr rfl fun j _ => congrArg (· ^ W i j) (h₃ i j))).trans ?_
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_psi (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left} (hL : L'.IsLB)
    (pr : Fin r → (B' ⟶ Q.B)) {w : LB.Iso L' (LB.LinComb Q.M.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → Q.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ Q.c (y i)) :
    ∃ t : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x.left) (fun _ => -1)), t.IsGen ∧
      ∀ z J J', Good Q.M.L z J → Good L' z J' → val t (𝟙 _) z J' =
        gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), J' x.left)) *
          ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  let z₀ : (TK R).left := closedPoint (FractionRing R)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good _ Q.M.isLB z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J₁, hJ₁, -⟩ := exists_good _ hL z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨t, ht, hv⟩ := exists_gen_val (F := FractionRing R) hL (K := PUnit) (fun _ => x.left) (fun _ => -1) hJ₁
    (gm x.left z₀ _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), J₁ x.left)) *
      ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z₀ J₀ ^ W i j)
  refine ⟨t, ht, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  have a := gen_trans ht (𝟙 (TK R).left) z₀ (hJ'.mem (fun _ : PUnit => x.left) _) (hJ₁.mem (fun _ : PUnit => x.left) _)
  have b : trF (L := L') (fun _ : PUnit => x.left) (fun _ => -1) (𝟙 (TK R).left) z₀ (fun _ => J' (𝟙 _ ≫ x.left))
      (fun _ => J₁ (𝟙 _ ≫ x.left)) = (gm x.left z₀ _ (L'.g (J' x.left) (J₁ x.left)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp]
  exact (a.trans (congrArg₂ (· * ·) b hv)).trans
    (formula_trans Q W pr hw x y hx z₀ J J₀ hJ hJ₀ (J' x.left) (J₁ x.left) (hJ' _) (hJ₁ _)).symm

end GlobalTheory.Mum.TensPol

noncomputable section
namespace GlobalTheory.Mum.TensPol

def cpt {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)}
    {pr : Fin r → (A' ⟶ Q.B)} (lim : IsLimit (Fan.mk A' pr)) (y : Fin r → Q.X) : 𝟙_ (Over (Sp R)) ⟶ A' :=
  lim.lift (Fan.mk _ fun i => Q.c (y i))

theorem cpt_pr {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)}
    {pr : Fin r → (A' ⟶ Q.B)} (lim : IsLimit (Fan.mk A' pr)) (y : Fin r → Q.X) (i : Fin r) : cpt lim y ≫ pr i = Q.c (y i) :=
  lim.fac (Fan.mk _ fun i => Q.c (y i)) ⟨i⟩

theorem cpt_add {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)} [GrpObj A']
    {pr : Fin r → (A' ⟶ Q.B)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk A' pr)) (a b : Fin r → Q.X) :
    cpt lim (a + b) = cpt lim a * cpt lim b := by
  refine lim.hom_ext fun i => ?_
  have := hpr i.as
  change cpt lim (a + b) ≫ pr i.as = (cpt lim a * cpt lim b) ≫ pr i.as
  rw [MonObj.mul_comp, cpt_pr, cpt_pr, cpt_pr]
  exact Q.c_add _ _

theorem cpt_zero {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)} [GrpObj A']
    {pr : Fin r → (A' ⟶ Q.B)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk A' pr)) :
    cpt lim (0 : Fin r → Q.X) = η[A'] := by
  refine lim.hom_ext fun i => ?_
  have := hpr i.as
  change cpt lim 0 ≫ pr i.as = η[A'] ≫ pr i.as
  rw [cpt_pr, IsMonHom.one_hom]
  have h := Q.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem exists_tensPol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) →
  ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
  ∃ (D' : DegData R (maximalIdeal R)) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) ∧
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) ∧ w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j := by
  intro R _ _ _ hR Q hQ r W hW hdet
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨P', pr, hpr, ⟨lim⟩, ⟨w, hw⟩⟩ := _root_.GlobalTheory.Mum.TensPow.exists_pow_data_polAV R Q W hW hdet
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P'
  obtain ⟨rig, hrig, hrv⟩ := rig_exists Q.M.isLB W P'.isLB pr hpr w hw
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have cub := (hL.cube _ P' ⟨P'.L, rig, P'.isLB, hrig⟩ rfl).1.some
  choose psi hpsi hpv using fun y : Fin r → Q.X =>
    exists_psi Q W P'.isLB pr hw (toUnit (TK R) ≫ cpt lim y) y (fun i => by rw [Category.assoc, cpt_pr])
  let D' : DegPre R :=
    { P := P'
      rig := rig
      rig_gen := hrig
      cub := cub
      sym := sym
      sym_gen := hsym
      sym_rig := hsr
      X := Fin r → Q.X
      c := cpt lim
      c_add := cpt_add hpr lim
      psi := psi
      psi_gen := hpsi }
  have hv : ∀ (y : D'.X) z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' =
      gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau ((AddEquiv.refl D'.X) y i) ((AddEquiv.refl D'.X) y j)) (𝟙 _) z J ^ W i j :=
    fun y z J J' hJ hJ' => hpv y z J J' hJ hJ'
  have hc : ∀ (y : D'.X) i, D'.c y ≫ pr i = Q.c ((AddEquiv.refl D'.X) y i) := fun y i => cpt_pr lim y i
  have h0 : ∀ (z : (TK R).left) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J' →
      val (D'.psi 0) (𝟙 _) z J' * val D'.rigK (𝟙 _) z J' = 1 := by
    intro z J' hJ'
    obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have h1 := hpv 0 z J J' hJ hJ'
    have h2 := hrv z J J' hJ hJ'
    have hprod : (∏ i, ∏ j, val (Q.tau ((0 : Fin r → Q.X) i) ((0 : Fin r → Q.X) j)) (𝟙 _) z J ^ W i j) = 1 :=
      Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
        rw [show (0 : Fin r → Q.X) i = 0 from rfl, Q.val_tau_zero _ z J hJ, one_zpow]
    rw [hprod, _root_.mul_one] at h1
    show val (psi 0) (𝟙 _) z J' * val (LB.pullGen P'.L _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' = 1
    rw [h1, _root_.mul_comm]
    have hz := cpt_zero hpr lim (Q := Q)
    revert h2
    generalize cpt lim 0 = x at hz ⊢
    subst hz
    exact id
  obtain ⟨hpos, htend⟩ := _root_.GlobalTheory.Mum.TensPol.psi_pos_tendsto R hR Q D' W pr hpr lim (AddEquiv.refl _) hc w hw hv hW hQ
  exact ⟨⟨D', _root_.GlobalTheory.PolTensEven.main R hR Q D' W pr hpr lim (AddEquiv.refl _) hc w hw hv,
    _root_.GlobalTheory.TensPolBimult.main R hR Q D' W pr hpr lim (AddEquiv.refl _) hc w hw hv h0, hpos, htend⟩,
    pr, AddEquiv.refl _, w, hpr, ⟨lim⟩, hc, hw, hv⟩

end GlobalTheory.Mum.TensPol
