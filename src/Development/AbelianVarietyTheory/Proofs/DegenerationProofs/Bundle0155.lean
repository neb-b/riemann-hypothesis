module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.Ex.OneGen


open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in
theorem exists_sec_pull_locus {X Y : Scheme.{0}} {L : LB X} (s : LB.Sec L) (φ : Y ⟶ X) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)),
      nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        have g : (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => 1) (𝟙 Y) z j j').val =
            gs (𝟙 Y ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val := by
          refine Eq.trans ?_ (gs_unit _ z _ hm _).symm
          exact congrArg Units.val ((Fin.prod_univ_one _).trans (zpow_one _))
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans g))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  have b : ∀ (j : Fin 1 → L.ι) (y : Y), y ∈ Y.basicOpen (s'.f j) ↔
      y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ∧ φ y ∈ X.basicOpen (s.f (j 0)) := fun j y => by
    change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) ↔ _
    rw [Scheme.basicOpen_res]
    exact and_congr_right fun _ => (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f (j 0))) y).symm
  refine ⟨s', SetLike.ext fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, ((b j y).1 hj).2⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ nonzeroLocus s from h)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (b _ y).2
      ⟨Set.mem_iInter.2 fun _ => X.basicOpen_le _ hi, hi⟩⟩

theorem isUnit_sval_iff {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem nz_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (hσ : ∀ y : T.left, ∃ g, (fst T G).left g = y ∧ g ∈ nonzeroLocus σ)
    {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (h : Over.mk χ ⟶ T) :
    NZ G L χ (VVRank.pullS G _ h σ) := by
  obtain ⟨g, hg, hn⟩ := hσ (h.left (closedPoint V))
  have P : IsPullback (h ▷ G).left (fst (Over.mk χ) G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w h]
      exact (IsPullback.of_hasPullback χ G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  obtain ⟨g', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P g (closedPoint V) hg
  refine ⟨g', h₂, ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL g'
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T G).left) σ (𝟙 _ ≫ (h ▷ G).left) g' hJ).2
    (by rw [Category.id_comp, h₁]; exact hn)
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk χ) G).left) _ (𝟙 _) g' hJ).1
    ((congrArg IsUnit (VVRank.sv_pullS G _ h σ (𝟙 _) g' hJ)).mpr u)

theorem exists_sec_nz_up {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {L₀ : LB G.left} {L₁ : LB A.left}
    {w : LB.Iso L₁ (L₀.pull φ)} (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h : GlobalTheory.LN.ThetaNZ A L₁) :
    ∃ σ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) (Over.mk f)),
      ∀ y : (Over.mk f).left, ∃ g, (fst (Over.mk f) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨θ, hθ⟩ := h
  let T : Over S' := Over.mk (𝟙 S')
  obtain ⟨s, hs⟩ := exists_sec_pull_locus θ (snd T A).left
  have hτ : (𝟙 S' : T.left ⟶ (Over.mk f).left) ≫ (Over.mk f).hom = T.hom ≫ f := rfl
  have : IsIso (𝟙 S' : T.left ⟶ (Over.mk f).left) := IsIso.id S'
  obtain ⟨σ, hσ⟩ := exists_secRel_up (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ hw hL₀ hL₁ (a := ((1 : ℕ) : ℤ)) s
  refine ⟨σ, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hθ y
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) y g hg.symm
  have hz : z ∈ nonzeroLocus s := by
    rw [hs]
    change pullback.snd T.hom A.hom z ∈ nonzeroLocus θ
    rw [h₂]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨J, hJ⟩ := exists_good' hL₀ z
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ z
  have e₁ := psi_fst' (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ
  refine ⟨psi (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, e₁]
    exact h₁
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T A).left) s (𝟙 _) z hJ').2 hz
  have e := hσ _ (𝟙 _) z J J' hJ hJ'
  rw [Category.id_comp] at e
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk f) G).left) σ _ z hJ).1
    ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))

theorem exists_nz_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  intro h₁ h₂ E _ _ _ H S t W _ _ _ χ t' m hp
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨σ, hσ⟩ := exists_sec_nz_up m.cart hw t.PP.isLB t'.PP.isLB
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt h₁ h₂ E H W t' hp)
  exact ⟨σ, fun W' _ _ i χ' h => nz_pullS t.G t.PP.isLB σ hσ χ' _⟩

end GlobalTheory.Ex.OneGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryTwistByRootsOfDataIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem exists_tateIsoQ_twJ : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  intro hGt hWp
  unfold BrGtSt AllN at hGt
  unfold BrWpSt AllN at hWp
  unfold AllD
  intro E _ _ _ H D R R' _ _ _ _ F _ _ _ _ A D' _ oa' hE' hB' N' ν' k β u r J hr hact
  unfold ActCompat at hact
  have hG := hGt R A.D₀ A.even A.bimult F A.N A.ν
  have hG' := hGt R' D' hE' hB' F N' ν'
  have hW := hWp R A.D₀ A.even A.bimult F A.N A.ν
  have hW' := hWp R' D' hE' hB' F N' ν'
  have hI := _root_.GlobalTheory.Relabel.twJ_mulEquiv F A.N N' k β u J
  choose τ hτ using fun n (hn : 0 < n) => hI.1 (r n) n (hr.pow hn)
  have hex : ∀ n (a : D.La), ∃ p : QkPt D' F n, ∀ hn : 0 < n, ν'.QPt p (τ n hn (A.q n a)) := by
    intro n a
    by_cases hn : 0 < n
    · obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a))
      exact ⟨p, fun _ => hp⟩
    · obtain ⟨p, -⟩ := (hG'.2.2.2.2 n).2.1 1
      exact ⟨p, fun h => absurd h hn⟩
  choose ev hev using hex
  let I' : TateIsoQ D D' oa' F :=
    { ζ := A.I.ζ
      ζ_prim := A.I.ζ_prim
      ζ_pow := A.I.ζ_pow
      ev := ev
      add := by
        intro n hn a b
        obtain ⟨q₀, hy, hadd, heq⟩ := A.I.add n hn a b
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have hw : w₀ = A.q n a * A.q n b := by
          apply Subtype.ext
          apply Prod.ext
          · apply Multiplicative.toAdd.injective
            apply A.ν.eX.injective
            rw [hw₀.1, hy, ← (A.hq n a).1, ← (A.hq n b).1, ← map_add (f := _)]
            rfl
          · exact (hG.2.2.1 _ _ _ _ _ _ (A.hq n a).2 (A.hq n b).2 hw₀.2).mp hadd
        have hqe := ((hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n (a + b))).mp heq
        rw [hw] at hqe
        have hqe' := ((hτ n hn).2.1 _ _).mp hqe
        rw [map_mul] at hqe'
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn (A.q n a) * τ n hn (A.q n b))
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev n a hn).1, ← (hev n b hn).1, ← map_add (f := _)]
          rfl
        · exact (hG'.2.2.1 _ _ _ _ _ _ (hev n a hn).2 (hev n b hn).2 hp.2).mpr rfl
        · exact ((hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n (a + b) hn)).mpr hqe'
      lin := by
        intro n hn x a
        exact hact n hn x _ _ _ _ _ _ _ _ (A.I.lin n hn x a) (A.hq n a) (A.hq n (x • a))
          (((hτ n hn).1 _ _).mp rfl) (((hτ n hn).1 _ _).mp rfl) (hev n a hn) (hev n (x • a) hn)
      ker := by
        intro n hn a b
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) (hev n b hn), ← (hτ n hn).2.1,
          ← (hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) (A.hq n b)]
        exact A.I.ker n hn a b
      onto := by
        intro n hn p
        obtain ⟨v, hv, -⟩ := (hG'.2.2.2.2 n).1 p
        obtain ⟨p₀, hp₀⟩ := (hG.2.2.2.2 n).2.1 ((τ n hn).symm v)
        obtain ⟨a, ha⟩ := A.I.onto n hn p₀
        refine ⟨a, ?_⟩
        rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ (hev n a hn) hv]
        have h := ((hτ n hn).2.1 _ _).mp (((hG.2.2.2.2 n).2.2 _ _ _ _ (A.hq n a) hp₀).mp ha)
        rwa [MulEquiv.apply_symm_apply] at h
      tower := by
        intro n m hn hm a
        have hnm : 0 < n * m := Nat.mul_pos hn hm
        obtain ⟨q₀, hy, hns, heq⟩ := A.I.tower n m hn hm a
        obtain ⟨w₀, hw₀, -⟩ := (hG.2.2.2.2 n).1 q₀
        have h1 : w₀.1.1 = (A.q (n * m) a).1.1 := by
          apply Multiplicative.toAdd.injective
          apply A.ν.eX.injective
          rw [hw₀.1, hy, (A.hq (n * m) a).1]
        have h2 : w₀.1.2 = (A.q (n * m) a).1.2 ^ m :=
          (GtValues.isNsmul_val A.ν m (A.hq (n * m) a).2 hw₀.2).mp hns
        obtain ⟨e1, e2⟩ := hI.2 (r n) (r (n * m)) n (n * m) m w₀ (A.q (n * m) a) (τ n hn w₀)
          (τ (n * m) hnm (A.q (n * m) a)) (hr.2 n m hn hm) h1 h2 (((hτ n hn).1 _ _).mp rfl)
          (((hτ (n * m) hnm).1 _ _).mp rfl)
        obtain ⟨p, hp⟩ := (hG'.2.2.2.2 n).2.1 (τ n hn w₀)
        refine ⟨p, ?_, ?_, ?_⟩
        · rw [← hp.1, ← (hev (n * m) a hnm).1, e1]
        · exact (GtValues.isNsmul_val ν' m (hev (n * m) a hnm).2 hp.2).mpr e2
        · rw [(hG'.2.2.2.2 n).2.2 _ _ _ _ hp (hev n a hn), ← (hτ n hn).2.1,
            ← (hG.2.2.2.2 n).2.2 _ _ _ _ hw₀ (A.hq n a)]
          exact heq
      isom := by
        intro n hn a b
        have h1 : 1 ≤ n := hn
        rw [hW' n h1 _ _ _ _ _ (hev n a hn) (hev n b hn), (hτ n hn).2.2]
        exact (hW n h1 _ _ _ _ _ (A.hq n a) (A.hq n b)).mp (A.I.isom n hn a b) }
  exact ⟨I', rfl, fun j hj x => ⟨τ j hj (A.q j x), ((hτ j hj).1 _ _).mp rfl, hev j x hj⟩⟩

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModelValuedExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Ex.ExtModel

theorem exists_extend {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (V : ValuationSubring F)
    {K : Type} [Field K] [CharZero K] (b : V →+* K) : ∃ bF : F →+* K, ∀ x : V, bF x = b x := by
  have hb : Function.Injective b := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : IsAlgebraic ℤ (x : F) := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have h2 : IsAlgebraic ℤ x :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 h1
    refine Ideal.comap_ne_bot_of_algebraic_mem (I := RingHom.ker b) h0 hx h2 ?_
    refine (Submodule.eq_bot_iff _).2 fun n hn => ?_
    have h3 : b (algebraMap ℤ V n) = 0 := hn
    simpa using h3
  exact ⟨IsFractionRing.lift (K := F) hb, fun x => IsFractionRing.lift_algebraMap (K := F) hb x⟩

theorem mem_of_pow_mem {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn.ne').1 h

theorem exists_mdl_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] (A : Lift a K) (o : Full D K), o.ρ = A.ρ → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra (FractionRing W) C], CDV W → CExt W (IsLocalRing.maximalIdeal W) C → ∀ (K₁ : Type) [Field K₁] [Algebra (FractionRing W) K₁] [Algebra.IsAlgebraic (FractionRing W) K₁] (gam : K₁ →+* C) (e : K →+* K₁) (φ : O' →+* W), (∀ x, gam (algebraMap (FractionRing W) K₁ x) = algebraMap (FractionRing W) C x) → (∀ x, e (algebraMap (FractionRing O') K (algebraMap O' _ x)) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x))) → ∀ o' : Full D C, FullExt (gam.comp e) o o' → ∃ (M : Mdl o') (f : W →+* M.W), ∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing W) C (algebraMap _ _ x) := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ K _ _ _ A o hρ C _ _ _ _ _ W _ _ _ _ hW hC K₁ _ _ _
    gam e φ hg he o' hext
  have : CharZero K := o.charZero
  have := c.fin
  obtain ⟨bF, hbF⟩ := exists_extend (c.V W₀)
    (((algebraMap (FractionRing O') K).comp (algebraMap O' (FractionRing O'))).comp b)
  obtain ⟨ν, h₀, hν₁, hν₂⟩ := GlobalTheory.ReZeta.exists_exponent o.I.ζ A.I.ζ o.I.ζ_prim o.I.ζ_pow A.I.ζ_prim A.I.ζ_pow
  obtain ⟨g, rfl⟩ := GlobalTheory.ReZeta.exists_sim D ν hν₁ hν₂
  let o₁ : Full D K := withI o (GlobalTheory.LevelTwist.twist o.I g fun n m hn hm => ⟨hν₂ n m hn hm, hν₁ n hn⟩)
  let o₁' : Full D C := withI o' (GlobalTheory.LevelTwist.twist o'.I g fun n m hn hm => ⟨hν₂ n m hn hm, hν₁ n hn⟩)
  have hext₁ : FullExt (gam.comp e) o₁ o₁' := by
    obtain ⟨p₁, p₂, ψ, p₃, p₄, p₅, p₆⟩ := hext
    refine ⟨p₁, fun n hn => ?_, ψ, p₃, p₄, p₅, fun n v hn => p₆ n (g.f n v) hn⟩
    change ((o'.I.ζ n ^ g.ν n : Cˣ) : C) = gam.comp e ((o.I.ζ n ^ g.ν n : Kˣ) : K)
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, p₂ n hn]
  obtain ⟨q₁, -, q₃⟩ := _root_.GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K bF
  obtain ⟨y, ⟨hy, hyo⟩, -⟩ := q₁ o₁ (fun r hr => by
      have hm : r ∈ c.V W₀ := mem_of_pow_mem _ two_pos (by
        have : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [hr] using H.sqrt_neg_disc_sq)
        rw [this]; exact neg_mem (natCast_mem _ _))
      exact hρ.trans ((A.ρ_eq ⟨r, hm⟩ hr).trans (hbF ⟨r, hm⟩).symm))
    (fun z hz => by
      have hm : z ∈ c.V W₀ := mem_of_pow_mem _ l.A_pos (by
        have : z ^ l.A = 1 := Subtype.ext (by
          simpa [hz, zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one)
        rw [this]; exact one_mem _)
      exact (congrArg Units.val (h₀ l.A l.A_pos)).trans ((A.ζ_eq ⟨z, hm⟩ hz).trans (hbF ⟨z, hm⟩).symm))
  have hF := q₃ C (gam.comp e) y o₁ o₁' hyo hext₁
  rw [spMap_comp', Category.assoc] at hF
  have hs : (spMap e ≫ y) ≫ Y.j ≫ Y.s = spMap (algebraMap (FractionRing W) K₁) ≫ jK W ≫ spMap (φ.comp b) := by
    rw [Model.j_s, Category.assoc, ← Category.assoc y, hy, ← spMap_comp', ← spMap_comp']
    change _ = spMap _ ≫ spMap (algebraMap W (FractionRing W)) ≫ _
    rw [← spMap_comp', ← spMap_comp']
    refine congrArg spMap (RingHom.ext fun x => ?_)
    exact (congrArg e (hbF x)).trans (he (b x))
  obtain ⟨M, f, -, -, -, hf, -⟩ := GlobalTheory.Ex.UnifModel.exists_mdl h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y C W hW hC K₁ gam hg
    (spMap e ≫ y) (φ.comp b) hs o₁' hF
  exact ⟨{ W := M.W, cdv := M.cdv, ext := M.ext, t := M.t, P := M.P, φ := M.φ, cart := M.cart, lb := M.lb, act := M.act },
    f, hf⟩

end GlobalTheory.Ex.ExtModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePow
section
namespace GlobalTheory

theorem exists_valuedField_centred_subalgebra (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K]
    (u : R) (hu : u ≠ 0) (A : Subalgebra R K) (hA : A.FG) (P : Ideal A) (hP : P.IsPrime)
    (huP : algebraMap R A u ∈ P) :
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (gam : K →+* C), (∀ x ∈ A, ‖gam x‖ ≤ 1) ∧
        ∀ x : A, x ∈ P → ‖gam (x : K)‖ < 1 := by
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hinj : Function.Injective (algebraMap R A) := by
    intro a b hab
    apply hinjK
    have := congrArg (fun x : A => (x : K)) hab
    simpa using this
  haveI : IsNoetherianRing A := isNoetherianRing_of_fg hA
  haveI : Algebra.IsAlgebraic A K := Algebra.IsAlgebraic.extendScalars hinj
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 Subtype.val_injective
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at huP
    exact hu (hinj (by rw [huP, map_zero]))
  obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ := _root_.GlobalTheory.Ex.exists_complete_isAlgClosed_centred_at_prime A K P hP hne
  exact ⟨C, i1, i2, i3, i4, gam, fun x hx => h1 ⟨x, hx⟩, fun x hx => h2 x hx⟩

theorem exists_valuedField_centre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  intro R K _ _ _ _ _ _ _ _ u hum hu R₁ hfin S hS e
  have hinjK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  have hR : ∀ r, S.valuation (algebraMap R K r) ≤ 1 := fun r =>
    (S.valuation_le_one_iff _).2 (hS r)
  have hR₁ : ∀ x ∈ R₁, S.valuation x ≤ 1 := by
    intro x hx
    have hint : IsIntegral R x := by
      have h := (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : R₁)).map R₁.val
      simpa using h
    letI : Algebra R S := ((algebraMap R K).codRestrict S.toSubring hS).toAlgebra
    haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint' : IsIntegral S x := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).1 hint'
    rw [← hy]
    exact (S.valuation_le_one_iff _).2 y.2
  have hfg : (Subalgebra.toSubmodule R₁).FG := Module.Finite.iff_fg.1 hfin
  let q : Ideal R₁ :=
    { carrier := {x | S.valuation (x : K) < 1}
      add_mem' := fun {a b} ha hb => by
        simpa using S.valuation.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hx' : S.valuation (x : K) < 1 := hx
        show S.valuation ((c : K) * (x : K)) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ c.2)) hx' }
  have hq : ∀ x : R₁, x ∈ q ↔ S.valuation (x : K) < 1 := fun _ => Iff.rfl
  have hqp : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hq]; simp
    · intro a b hab
      by_contra hcon
      rw [not_or, hq, hq, not_lt, not_lt] at hcon
      rw [hq, Subalgebra.coe_mul, map_mul, le_antisymm (hR₁ _ a.2) hcon.1,
        le_antisymm (hR₁ _ b.2) hcon.2] at hab
      simp at hab
  by_cases hv : S.valuation (algebraMap R K u) = 1
  ·
    set U : K := algebraMap R K u with hU
    have hU0 : U ≠ 0 := fun h => hu (hinjK (by rw [← hU, h, map_zero]))
    let Q : Submodule R K := (q.restrictScalars R).map R₁.val.toLinearMap
    have hQ : Q.FG := by
      haveI : IsNoetherian R R₁ := isNoetherian_of_isNoetherianRing_of_finite R R₁
      exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    let N : Submodule R K := Subalgebra.toSubmodule R₁ ⊔
      Q.map (LinearMap.mulRight R (U ^ (e + 1))⁻¹)
    have hN : N.FG := Submodule.FG.sup hfg (hQ.map _)
    let A : Subalgebra R K := Algebra.adjoin R (N : Set K)
    have hA : A.FG := by
      obtain ⟨s, hs⟩ := hN
      refine ⟨s, ?_⟩
      show _ = Algebra.adjoin R (N : Set K)
      rw [← hs, Algebra.adjoin_span]
    have hinv : ∀ x ∈ A, ∃ a ∈ R₁, S.valuation (x - a) < 1 := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
        refine ⟨a, ha, ?_⟩
        have hg' : S.valuation (g : K) < 1 := hg
        simpa [hv] using hg'
      | algebraMap r => exact ⟨_, R₁.algebraMap_mem r, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a + b, R₁.add_mem ha hb, ?_⟩
        rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
        exact S.valuation.map_add_lt hx hy
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha, hx⟩ := hx
        obtain ⟨b, hb, hy⟩ := hy
        refine ⟨a * b, R₁.mul_mem ha hb, ?_⟩
        rw [show x * y - a * b = (x - a) * (y - b) + (b * (x - a) + a * (y - b)) by ring]
        refine S.valuation.map_add_lt ?_ (S.valuation.map_add_lt ?_ ?_) <;> rw [map_mul]
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hy
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ hb)) hx
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hR₁ _ ha)) hy
    have hnu : ¬ IsUnit (algebraMap R A u) := by
      intro hun
      obtain ⟨x, hx⟩ := hun.exists_right_inv
      have hx' : U * (x : K) = 1 := by
        have := congrArg (fun x : A => (x : K)) hx
        simpa using this
      obtain ⟨a, ha, hxa⟩ := hinv x x.2
      obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hqp.ne_top
      have hMc : (M.comap (algebraMap R R₁)).IsMaximal := by
        letI : M.IsMaximal := hM
        exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
      have huM : algebraMap R R₁ u ∈ M := by
        rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hMc]; exact hum
      have h1 : (1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) ∈ q := by
        rw [hq]
        have : ((1 - algebraMap R R₁ u * ⟨a, ha⟩ : R₁) : K) = U * (x - a) := by
          rw [mul_sub, hx']; simp [hU]
        rw [this, map_mul, hv, one_mul]
        exact hxa
      apply hM.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using M.add_mem (hqM h1) (M.mul_mem_right (⟨a, ha⟩ : R₁) huM)
    obtain ⟨P, hP, huP⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu A hA P hP.isPrime huP
    have hgu : ‖gam U‖ < 1 := h2 _ huP
    refine ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (A.algebraMap_mem r), hgu, ?_⟩
    intro f hf hvf
    have hmem : f * (U ^ (e + 1))⁻¹ ∈ A :=
      Algebra.subset_adjoin (Submodule.mem_sup_right
        (Submodule.mem_map.2 ⟨f, Submodule.mem_map.2 ⟨⟨f, hf⟩, hvf, rfl⟩, rfl⟩))
    have hle : ‖gam f‖ ≤ ‖gam U‖ ^ (e + 1) := by
      have hf' : f = f * (U ^ (e + 1))⁻¹ * U ^ (e + 1) := by field_simp
      have h3 := h1 _ hmem
      rw [hf', map_mul, norm_mul, map_pow, norm_pow]
      exact mul_le_of_le_one_left (by positivity) h3
    refine ⟨hle.trans_lt (pow_lt_one₀ (norm_nonneg _) hgu (by omega)), fun _ => hle.trans ?_⟩
    exact pow_le_pow_of_le_one (norm_nonneg _) hgu.le (by omega)
  · have huq : algebraMap R R₁ u ∈ q := lt_of_le_of_ne (hR u) hv
    obtain ⟨C, i1, i2, i3, i4, gam, h1, h2⟩ :=
      exists_valuedField_centred_subalgebra R K u hu R₁ (Subalgebra.fg_of_fg_toSubmodule hfg)
        q hqp huq
    exact ⟨C, i1, i2, i3, i4, gam, fun r => h1 _ (R₁.algebraMap_mem r), h2 _ huq,
      fun f hf hvf => ⟨h2 ⟨f, hf⟩ hvf, fun h => absurd h hv⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCondition_of_one_algClosed_field : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  first | exact @GlobalTheory.LevelField.toA_of_toA | exact GlobalTheory.LevelField.toA_of_toA | (intros; apply GlobalTheory.LevelField.toA_of_toA <;> assumption)
end

