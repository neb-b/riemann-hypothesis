module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeneratingSectionFiniteExtNormalDomainIsBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGenBasis

theorem pullTo_injective {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (p : Y' ⟶ Y) (e : ∀ k, p ≫ φ k = φ' k) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    {s t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, (VVRank.pullTo s p e).f j = (VVRank.pullTo t p e).f j) (j) :
    s.f j = t.f j := by
  obtain rfl : (fun k => p ≫ φ k) = φ' := funext e
  refine p.app_injective _ (fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L (fun k => p ≫ φ k) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact (gs_res _ y _ hy' _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j)).trans (gs_res _ y _ hy' _))

theorem pullM_injective {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) [IsSchemeTheoreticallyDominant h.left] [QuasiCompact h.left] :
    Function.Injective (VVRank.pullM G L a h) := by
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w]
      exact (IsPullback.of_hasPullback T'.hom G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have : Flat (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have : IsSchemeTheoreticallyDominant (h ▷ G).left := .of_isPullback hp.flip
  have : QuasiCompact (h ▷ G).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  intro s t e
  exact Subtype.ext (funext (pullTo_injective (s := SecM.toSec G s) (t := SecM.toSec G t) (h ▷ G).left
    (fun _ => VVRank.whisker_snd_left G h) fun j => congrFun (congrArg Subtype.val e) j))

theorem exists_eq_mul {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : FractionRing W} (ha : a ≠ 0) {r : W'}
    (h : i' b = algebraMap W' _ r * i' a) : ∃ r₀ : W, b = algebraMap W _ r₀ * a := by
  have h₁ : i' (b / a) = algebraMap W' _ r := by
    rw [map_div₀, h, mul_div_cancel_right₀ _ ((map_ne_zero i').2 ha)]
  obtain ⟨p, hp, h₂⟩ := hf.to_isIntegral r
  have h₃ : IsIntegral W (b / a) := ⟨p, hp, i'.injective (by
    rw [Polynomial.hom_eval₂, hi, h₁, ← Polynomial.hom_eval₂, h₂, map_zero, map_zero])⟩
  obtain ⟨r₀, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h₃
  exact ⟨r₀, by rw [hr, div_mul_cancel₀ _ ha]⟩

theorem exists_fractionMap {W W' : Type} [CommRing W] [IsDomain W] [CommRing W'] [IsDomain W'] (i : W →+* W')
    (hi : Function.Injective i) : ∃ i' : FractionRing W →+* FractionRing W',
      i'.comp (algebraMap W _) = (algebraMap W' _).comp i := by
  have hg : Function.Injective ((algebraMap W' (FractionRing W')).comp i) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W' (FractionRing W')).comp hi
  refine ⟨IsFractionRing.lift (K := FractionRing W) hg, RingHom.ext fun x => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

theorem appTop_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) :=
  (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem inv_bijective (R : Type) [CommRing R] :
    Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

theorem exists_eq_mul_fn {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : Γ(Sp (FractionRing W), ⊤)} (ha : a ≠ 0)
    {r : Γ(Sp W', ⊤)} (h : (spMap i').appTop.hom b = (jK W').appTop.hom r * (spMap i').appTop.hom a) :
    ∃ r₀ : Γ(Sp W, ⊤), b = (jK W).appTop.hom r₀ * a := by
  obtain ⟨a, rfl⟩ := (inv_bijective _).2 a
  obtain ⟨b, rfl⟩ := (inv_bijective _).2 b
  obtain ⟨r, rfl⟩ := (inv_bijective _).2 r
  rw [appTop_inv, appTop_inv, appTop_inv, ← map_mul] at h
  obtain ⟨r₀, hr⟩ := exists_eq_mul i hf i' hi (a := a) (fun e => ha (by rw [e, map_zero]))
    ((inv_bijective (FractionRing W')).1 h)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r₀, by
    rw [appTop_inv (algebraMap W (FractionRing W)), ← map_mul, ← hr]⟩

theorem basis_of_square {A A' K K' M M' N N' : Type} [CommRing A] [CommRing A'] [CommRing K] [CommRing K'] [IsDomain K]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N'] [Module A M] [Module A' M'] [Module K N]
    [Module K' N'] {f : A →+* K} {g : A →+* A'} {f' : A' →+* K'} {g' : K →+* K'} (p : M →ₛₗ[f] N) (q : M →ₛₗ[g] M')
    (p' : M' →ₛₗ[f'] N') (q' : N →ₛₗ[g'] N') (hsq : ∀ x, q' (p x) = p' (q x)) (hp : Function.Injective p)
    (hf : Function.Injective f) (e : N) (h₀ : ∀ s, ∃! c : K, s = c • e) (h₁ : ∀ s, ∃! c : K', s = c • q' e) (σ : M)
    (hne : p σ ≠ 0) (hgen : ∀ s, ∃ r : A', q s = r • q σ)
    (hint : ∀ a b r, a ≠ 0 → g' b = f' r * g' a → ∃ r₀, b = f r₀ * a) :
    LinearIndependent A (fun _ : Fin 1 => σ) ∧ Submodule.span A (Set.range fun _ : Fin 1 => σ) = ⊤ := by
  obtain ⟨a, ha, -⟩ := h₀ (p σ)
  have ha0 : a ≠ 0 := fun h => hne (ha.trans (by rw [h, zero_smul]))
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc k => ?_, eq_top_iff.2 fun s _ => ?_⟩
  · rw [Fin.sum_univ_one] at hc
    rw [Subsingleton.elim k 0]
    have t := congrArg p hc
    rw [map_smulₛₗ, ha, smul_smul, map_zero] at t
    have t' := (h₀ 0).unique t.symm (zero_smul _ _).symm
    exact hf (((mul_eq_zero.1 t').resolve_right ha0).trans (map_zero _).symm)
  · obtain ⟨b, hb, -⟩ := h₀ (p s)
    obtain ⟨r, hr⟩ := hgen s
    have t := congrArg p' hr
    rw [map_smulₛₗ, ← hsq, ← hsq, ha, hb, map_smulₛₗ, map_smulₛₗ, smul_smul] at t
    obtain ⟨r₀, hr₀⟩ := hint a b r ha0 ((h₁ _).unique rfl t)
    have : s = r₀ • σ := hp (by rw [map_smulₛₗ, ha, hb, smul_smul, hr₀])
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

theorem basisAlong_of_isGenSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  intro S G _ _ L hL W W' _ _ _ _ _ i hinj hf χ σ hgen ⟨e, he⟩ hne
  obtain ⟨i', hi⟩ := exists_fractionMap i hinj
  have hsq : spMap i' ≫ jK W = jK W' ≫ spMap i := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  let hK : Over.mk (jK W ≫ χ) ⟶ Over.mk χ := Over.homMk (jK W) rfl
  let hI : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let hI' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ) := Over.homMk (spMap i') rfl
  let hK' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (jK W') (by
    change jK W' ≫ spMap i ≫ χ = spMap i' ≫ jK W ≫ χ
    rw [← Category.assoc, ← hsq, Category.assoc])
  have hsq' : hI' ≫ hK = hK' ≫ hI := Over.OverMorphism.ext hsq
  have : IsSchemeTheoreticallyDominant hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).2
  have : QuasiCompact hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).1
  have hρ := pullM_injective G L ((1 : ℕ) : ℤ) hK
  have hid : spMap (RingHom.id (FractionRing W)) = 𝟙 _ := Spec.map_id _
  have h₀ : ∀ s : SecM G L ((1 : ℕ) : ℤ) (Over.mk (jK W ≫ χ)), ∃! c : Γ((Over.mk (jK W ≫ χ)).left, ⊤),
      s = c • SecM.ofSec G e := fun s => by
    have q := he _ (RingHom.id _) _ (by rw [hid, Category.id_comp]) s
    rwa [← VVRank.pullM_ofSec, show (Over.homMk (spMap (RingHom.id (FractionRing W))) _ :
      Over.mk (jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ)) = 𝟙 _ from Over.OverMorphism.ext hid, VVRank.pullM_id G hL] at q
  have h₁ : ∀ s, ∃! c : Γ((Over.mk (spMap i' ≫ jK W ≫ χ)).left, ⊤),
      s = c • VVRank.pullM G L ((1 : ℕ) : ℤ) hI' (SecM.ofSec G e) := he _ i' _ rfl
  have hdom : IsDomain Γ((Over.mk (jK W ≫ χ)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have key := basis_of_square (VVRank.pullM G L ((1 : ℕ) : ℤ) hK) (VVRank.pullM G L _ hI) (VVRank.pullM G L _ hK')
    (VVRank.pullM G L _ hI') (fun x => by rw [VVRank.pullM_comp G hL, VVRank.pullM_comp G hL, hsq']) hρ
    (hK.left.app_injective ⊤) _ h₀ h₁ (SecM.ofSec G σ) hne
    (fun s => (hgen (SecM.toSec G (VVRank.pullM G L _ hI s))).imp fun _ hr => Subtype.ext (funext hr))
    fun a b r ha h => exists_eq_mul_fn i hf i' hi ha h
  rw [← VVRank.pullM_id G hL _ (SecM.ofSec G σ)] at key
  exact (GlobalTheory.LN.PolFrames.basisAlong_iff G L 1 (𝟙 _) hL
    (b' := fun _ => VVRank.pullS G _ (𝟙 _) σ) fun _ => VVRank.isPullSec_pullS G _ _ σ).2 key

end GlobalTheory.Ex.OneGenBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPtNsmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.Ex.Arch.towerSt_of : _root_.GlobalTheory.Ex.BrGtSt → _root_.GlobalTheory.Ex.BrWpSt → _root_.GlobalTheory.Ex.Arch.PtSt → _root_.GlobalTheory.Ex.Arch.QkSt → _root_.GlobalTheory.Ex.Arch.WpSt → _root_.GlobalTheory.Ex.Arch.TowerSt := by
  intro hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.BrGtSt _root_.GlobalTheory.Ex.AllN at hGt
  unfold _root_.GlobalTheory.Ex.BrWpSt _root_.GlobalTheory.Ex.AllN at hWp
  unfold _root_.GlobalTheory.Ex.Arch.PtSt _root_.GlobalTheory.Ex.Arch.AllDict at hPt
  unfold _root_.GlobalTheory.Ex.Arch.QkSt _root_.GlobalTheory.Ex.Arch.AllDict at hQk
  unfold _root_.GlobalTheory.Ex.Arch.WpSt _root_.GlobalTheory.Ex.Arch.AllDict at hWA
  beta_reduce at hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.Arch.TowerSt _root_.GlobalTheory.Ex.AllD
  intro E _ _ _ H D R _ _ _ A B dd hl
  letI := H.starRing
  have hG := hGt R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hW := hWp R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hV := hPt (𝓞 E) A.N _ dd
  have hL := hQk (𝓞 E) A.N _ dd
  have hE := hWA (𝓞 E) A.N _ dd
  have hq := A.hq
  have hT := _root_.GlobalTheory.NestQVal.qval_add_tower E H D R A.D₀ A.oa A.even A.bimult ℂ A.I A.N A.ν A.q
    hG.1 hG.2.2.1 (fun k => ⟨(hG.2.2.2.2 k).1, (hG.2.2.2.2 k).2.2⟩) hq
  choose! f hf using fun n (hn : 0 < n) (a : D.La) => (hL n hn).1 (A.q n a)
  have hpow : ∀ (m : ℕ) v g, dd.IsPt v g → dd.IsPt (m • v) (g ^ m) := by
    obtain ⟨g₀, hg₀, hu⟩ := hV.1 0
    have h00 := hV.2.2.1 0 0 g₀ g₀ hg₀ hg₀
    rw [add_zero] at h00
    have hg₁ : g₀ = 1 := mul_eq_left.1 (hu _ h00)
    intro m v g hg
    induction m with
    | zero => simpa [hg₁] using hg₀
    | succ k ih => simpa [succ_nsmul, pow_succ] using hV.2.2.1 _ _ _ _ ih hg
  refine ⟨f, ?_, hf⟩
  unfold _root_.GlobalTheory.Ex.Arch.IsTower
  intro n hn
  obtain ⟨-, hRep, hmul, hmod⟩ := hL n hn
  have hQn := (hG.2.2.2.2 n).2.2
  have hadd : ∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e := fun a b =>
    (hmod _ _ _ _ (hmul _ _ _ _ (hf n hn a) (hf n hn b)) (hf n hn (a + b))).1 (hT.1 n hn a b)
  refine ⟨hadd, ?_, ?_, ?_, ?_, ?_⟩
  · intro c a
    obtain ⟨Q, hQy, hQg, hQe⟩ := A.I.lin n hn c a
    obtain ⟨p', hp', -⟩ := hRep (c • f n a)
    obtain ⟨hya, hga⟩ := hq n a
    obtain ⟨c'', hc'', -⟩ := hG.1 Q.g
    have hRa := hf n hn a
    have hv := hl.2 c _ _ _ _ _ hga hc'' hQg hRa.2
    rw [map_smul, ← _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul] at hv
    have hc : c'' = (p' : Multiplicative A.N.X × A.N.Gt).2 := (hV.1 _).unique hv hp'.2
    have hQp : A.ν.QPt Q p' := by
      refine ⟨?_, hc ▸ hc''⟩
      rw [hp'.1, _root_.GlobalTheory.AnArc.La.smul_y, hl.1, hQy, ← hya, hRa.1]
      unfold _root_.GlobalTheory.Ex.ArcF.act
      simp
    exact (hmod _ _ _ _ hp' (hf n hn (c • a))).1 ((hQn _ _ _ _ hQp (hq n (c • a))).1 hQe)
  · intro a
    obtain ⟨e₀, he₀⟩ : ∃ e, f n 0 = n • e := by
      obtain ⟨e, he⟩ := hadd 0 0
      rw [add_zero] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      calc f n 0 + n • e = (f n 0 + f n 0 + n • e) - f n 0 := by abel
        _ = 0 := by rw [← he, sub_self]
    have key : (∃ e, f n 0 = f n a + n • e) ↔ ∃ b, a = n • b := by
      rw [← hmod _ _ _ _ (hf n hn a) (hf n hn 0), ← hQn _ _ _ _ (hq n a) (hq n 0), A.I.ker n hn a 0]
      simp
    rw [← key]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [he₀, he, smul_sub]; abel⟩
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [smul_sub, ← he₀, he]; abel⟩
  · intro x
    obtain ⟨p, hp, -⟩ := hRep x
    obtain ⟨P, hP⟩ := (hG.2.2.2.2 n).2.1 p
    obtain ⟨a, ha⟩ := A.I.onto n hn P
    obtain ⟨e, he⟩ := (hmod _ _ _ _ (hf n hn a) hp).1 ((hQn _ _ _ _ (hq n a) hP).1 ha)
    exact ⟨a, e, he⟩
  · intro m hm a
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨p, hp, -⟩ := hRep (f (n * m) a)
    have hR := hf (n * m) hnm a
    have h1 : (p : Multiplicative A.N.X × A.N.Gt).1 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).1 := by
      apply Multiplicative.toAdd.injective
      rw [hp.1, hR.1]
    have h2 : (p : Multiplicative A.N.X × A.N.Gt).2 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).2 ^ m := by
      apply (hV.1 _).unique hp.2
      convert hpow m _ _ hR.2 using 1
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    obtain ⟨e, he⟩ := (hmod _ _ _ _ hp (hf n hn a)).1 (hT.2 n m hn hm a p h1 h2)
    exact ⟨-e, by rw [he, smul_neg]; abel⟩
  · intro a b
    rw [(hW n hn _ _ _ _ _ (hq n a) (hq n b)).1 (A.I.isom n hn a b)]
    exact hE n hn _ _ _ _ (hf n hn a) (hf n hn b)

end GlobalTheory.Ex.Arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section

namespace GlobalTheory.LevelField

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcDataDescent

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F₁ F₂ : Type} [Field F₀] [Field F₁]
    [Field F₂] [Algebra (FractionRing R) F₀] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R) F₂]
    {f : F₀ →+* F₁} {g : F₁ →+* F₂} {k : ℕ} {p₀ : QkPt D F₀ k} {p₁ : QkPt D F₁ k} {p₂ : QkPt D F₂ k}
    (h : QkExt f p₀ p₁) (h' : QkExt g p₁ p₂) : QkExt (g.comp f) p₀ p₂ := by
  refine ⟨h'.1.trans h.1, ?_, fun χ => corr_of_val D.P.isLB fun (y : Sp F₂) J hJ => ?_⟩
  · exact h'.2.1.trans ((congrArg (spMap g ≫ ·) h.2.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ p₀.g.b.left) (spMap_comp f g).symm)))
  · refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    exact congrArg (fun q => val (p₀.g.s χ) q y J) ((Category.assoc _ _ _).trans
      (congrArg (𝟙 (Sp F₂) ≫ ·) (spMap_comp f g).symm))

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {K : Type} [Fintype K] {pt pt' : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (hp : pt = pt') (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x)
    (z : Sp F) {J} (hJ : Good M z J) : val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  subst hp
  choose J₀ hJ₀ using fun χ : Sp F ⟶ B₀ => exists_chart hM₀ (χ z)
  have e := ((genRel_iff w t t₀ x z).1 h).2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  have e' := ((genRel_iff w t' t₀ x z).1 h').2 (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ))
    (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
  rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t' _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp])]
  exact mul_left_cancel (Units.ext (e.trans e'.symm))

variable {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {D : DegPre R} {D₀ : DegPre O'}
  {ψ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull ψ)} {k : ℕ}

theorem genRel_ext {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing O') F] [Algebra (FractionRing O') F'] {σ : F →+* F'}
    (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hσ₀ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')
    {q : QkPt D F k} {q' : QkPt D F' k} {q₀ : QkPt D₀ F k} {q₀' : QkPt D₀ F' k} (h : QkExt σ q q')
    (h₀ : QkExt σ q₀ q₀') {χ : D.X} {χ₀ : D₀.X} {x : F} (H : GenRel w (q.g.s χ) (q₀.g.s χ₀) x) :
    GenRel w (q'.g.s χ) (q₀'.g.s χ₀) (σ x) :=
  (genRel_congr D.P.isLB D₀.P.isLB w (gtφ_ext hσ h χ) (gtφ_ext hσ₀ h₀ χ₀) (q'.g.isGen _)
    (pullGen_isGen _ _ _ _ (q.g.isGen _) _) (q₀'.g.isGen _) (pullGen_isGen _ _ _ _ (q₀.g.isGen _) _)
    (fun _ _ hJ => val_corr hJ (h.2.2 χ) _) (fun _ _ hJ => val_corr hJ (h₀.2.2 χ₀) _) _).2
    ((genRel_pull_iff σ w _ _ x).2 H)

theorem eq_of_genRel {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] {f : O' →+* R}
    (gp : IsGrpPullback D.P.A D₀.P.A (spMap f) ψ) (e : D₀.X ≃+ D.X) {q q' : QkPt D F k} {q₀ : QkPt D₀ F k}
    {x : D₀.X → F} (hy : q.y = q'.y) (H : ∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (x χ))
    (H' : ∀ χ, GenRel w (q'.g.s (e χ)) (q₀.g.s χ) (x χ)) : q = q' := by
  have hb : q.g.b = q'.g.b :=
    Over.OverMorphism.ext (gp.1.hom_ext (((H 0).1 2).trans ((H' 0).1 2).symm) (by rw [Over.w, Over.w]))
  refine TorusExt.qk_ext hy (TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_)
  obtain ⟨χ, rfl⟩ := e.surjective χ
  exact val_eq_of_genRel D₀.P.isLB (by rw [hb]) (H χ) (H' χ) y hJ

theorem toA_of_toA : GlobalTheory.UT.LL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R O' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing O'] [IsDomain O'] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t) (D₀ : DegPre O'), D₀.TauBimult → ∀ (f : O' →+* R) (ψ : P.D.toPre.P.A.left ⟶ D₀.P.A.left) (w : LB.Iso P.D.toPre.P.L (D₀.P.L.pull ψ)) (e : D₀.X ≃+ P.D.toPre.X), IsGrpPullback P.D.toPre.P.A D₀.P.A (spMap f) ψ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀ (FractionRing O') k) (s : D₀.X → FractionRing R) (x₀ : Sp (FractionRing R) ⟶ P.A.A.left) (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C], Along f C → ∀ (q₀ : QkPt D₀ C k) (q : QkPt P.D.toPre C k) (x : TFK (R := R) C ⟶ P.A.A), QkExt (algebraMap _ C) p₀ q₀ → q.y = e q₀.y → (∀ χ, GenRel w (q.g.s (e χ)) (q₀.g.s χ) (algebraMap _ C (s χ))) → x.left = jFK (R := R) C ≫ x₀ → P.ToA C k q x → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F], Along f F → ∀ (q₀' : QkPt D₀ F k) (q' : QkPt P.D.toPre F k) (x' : TFK (R := R) F ⟶ P.A.A), QkExt (algebraMap _ F) p₀ q₀' → q'.y = e q₀'.y → (∀ χ, GenRel w (q'.g.s (e χ)) (q₀'.g.s χ) (algebraMap _ F (s χ))) → x'.left = jFK (R := R) F ≫ x₀ → P.ToA F k q' x' := by
  intro hL E _ _ _ H R O' _ _ _ _ _ I _ t P D₀ hB f ψ w e gp _ k hk p₀ s x₀ C _ _ _ _ hC q₀ q x h₀ hy hg hx hA
    F _ _ _ _ hF q₀' q' x' h₀' hy' hg' hx'
  obtain ⟨F', _, _, σ, τ, hστ⟩ := exists_common_field (algebraMap (FractionRing R) C) (algebraMap (FractionRing R) F)
  letI : Algebra (FractionRing R) F' := (σ.comp (algebraMap _ C)).toAlgebra
  letI : Algebra (FractionRing O') F' := (σ.comp (algebraMap _ C)).toAlgebra
  have hσ : σ.comp (algebraMap (FractionRing R) C) = algebraMap (FractionRing R) F' := rfl
  have hσ₀ : σ.comp (algebraMap (FractionRing O') C) = algebraMap (FractionRing O') F' := rfl
  have hτ : τ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := hστ.symm
  have hτ₀ : τ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' :=
    IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun a =>
      (congrArg τ (hF a).symm).trans ((RingHom.congr_fun hστ _).symm.trans (congrArg σ (hC a))))
  obtain ⟨r, hr, -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult σ hσ q
  obtain ⟨r', hr', -⟩ := TorusExt.existsUnique_qkExt P.D.tau_bimult τ hτ q'
  obtain ⟨r₀, hr₀, -⟩ := TorusExt.existsUnique_qkExt hB σ hσ₀ q₀
  obtain ⟨r₀', hr₀', -⟩ := TorusExt.existsUnique_qkExt hB τ hτ₀ q₀'
  have a := qkExt_trans h₀ hr₀
  have a' := qkExt_trans h₀' hr₀'
  rw [hσ₀] at a
  rw [hτ₀] at a'
  obtain rfl : r₀ = r₀' :=
    (TorusExt.existsUnique_qkExt hB (algebraMap (FractionRing O') F') (RingHom.ext fun _ => rfl) p₀).unique a a'
  obtain rfl : r = r' := eq_of_genRel gp e (q₀ := r₀) (x := fun χ => algebraMap (FractionRing R) F' (s χ))
    (by rw [hr.1, hr'.1, hy, hy', h₀.1, h₀'.1]) (fun χ => genRel_ext hσ hσ₀ hr hr₀ (hg χ))
    (fun χ => by
      have b := genRel_ext hτ hτ₀ hr' hr₀' (hg' χ)
      rwa [show τ (algebraMap (FractionRing R) F (s χ)) = algebraMap (FractionRing R) F' (s χ) from
        RingHom.congr_fun hτ _] at b)
  letI : Algebra C F' := σ.toAlgebra
  letI : Algebra F F' := τ.toAlgebra
  haveI : IsScalarTower (FractionRing R) C F' := IsScalarTower.of_algebraMap_eq' hσ.symm
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq' hτ.symm
  have hj : spMap σ ≫ jFK (R := R) C = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hσ)
  have hj' : spMap τ ≫ jFK (R := R) F = jFK (R := R) F' := (spMap_comp _ _).symm.trans (congrArg spMap hτ)
  have ex : TorsionExt.fieldMap (R := R) C F' ≫ x = TorsionExt.fieldMap (R := R) F F' ≫ x' := by
    refine Over.OverMorphism.ext ?_
    show spMap σ ≫ x.left = spMap τ ≫ x'.left
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hj, hj']
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr' x').2 ?_
  rw [← ex]
  exact (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow P.U hk hr x).1 hA

end GlobalTheory.LevelField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemMaximalIdeal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ModelBasis
open GlobalTheory.FieldBaseChange GlobalTheory.IntegralCombination GlobalTheory.ZH GlobalTheory.ZH.AdaptedSpan

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

theorem toGen_injective (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) : Function.Injective (toGen U k) := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have h₁ : IsSchemeTheoreticallyDominant (jK V) := h.2
  have h₂ : QuasiCompact (jK V) := h.1
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK V)) := inferInstance
  exact GlobalTheory.ConstFam.pullOver_injective_of_dominant _ _ _ _

theorem chart_sum {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of V)} {M : LB Y} {J : Type} [Fintype J]
    (c : J → V) (x : J → SecOver p M) (j : M.ι) :
    LB.Sec.f (∑ i, c i • x i : SecOver p M) j = ∑ i, resTop _ (scal p (c i)) * LB.Sec.f (x i) j :=
  map_sum (chartLin p M j) (fun i => c i • x i) _


open Classical in
theorem mem_maximalIdeal (hW : WeightIndepSt) (U : UnifPre (maximalIdeal V) D A G) {k : ℕ} {J : Type} [Fintype J]
    (σ : J → SecG U k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (hE : ∀ i, U.ExpandsAt 0 k (σ i) (f i)) (hz : ∀ i i₀, cls i ≠ cls i₀ → f i (cls i₀) = 0)
    (hB : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))) (c : J → V)
    (h : ∀ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (LB.Sec.f (∑ i, c i • σ i : SecG U k) j) = 0) (i₀ : J) :
    c i₀ ∈ maximalIdeal V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨g, hg⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 k (cls i₀) _).1
    (hW V _ D A G U 0 k _ _ h (expandsAt_sum U 0 k σ f hE c) (cls i₀))
  obtain ⟨a, ha, -⟩ := hB i₀ g
  let β : {i // cls i = cls i₀} → SecAb D.toPre k (cls i₀) := fun i => f i (cls i₀)
  have e₁ : (show SecAb D.toPre k (cls i₀) from g) = ∑ i, a i • β i :=
    SecOver.ext _ _ fun j => (ha j).trans (chart_sum a β j).symm
  have e₂ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) =
      ϖ ^ (0 + 1) • (show SecAb D.toPre k (cls i₀) from g) := SecOver.ext _ _ hg
  have e₃ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) = ∑ i : {i // cls i = cls i₀}, c i • β i := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
      Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
        (fun i _ => by rw [hz i i₀ i.2, smul_zero]), add_zero]
  have e₄ : (∑ i : {i // cls i = cls i₀}, c i • β i) = ∑ i, (ϖ ^ (0 + 1) * a i) • β i := by
    rw [← e₃, e₂, e₁, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have e₅ := (hB i₀ (∑ i : {i // cls i = cls i₀}, c i • β i : SecAb D.toPre k (cls i₀))).unique
    (y₁ := fun i => c i) (y₂ := fun i => ϖ ^ (0 + 1) * a i) (fun j => chart_sum _ β j)
    (fun j => by rw [e₄]; exact chart_sum _ β j)
  have e₆ : c i₀ = ϖ ^ (0 + 1) * a ⟨i₀, rfl⟩ := congrFun e₅ ⟨i₀, rfl⟩
  rw [e₆, zero_add, pow_one]
  exact Ideal.mul_mem_right _ _ hϖ.not_isUnit

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f → ∃ σ : Fin r → H0 U.LG.L k, (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧ IsBasisH σ := by
  intro hL V _ _ _ D Q A G _ _ U k hk r cls mu f ⟨⟨_, h₂, h₃, _⟩, h₅, h₆, h₇⟩
  have ex : ∀ i, ∃ σ : SecG U.toUnifPre k, ∀ e, U.ExpandsAt e k σ (f i) := fun i => by
    obtain ⟨s, hs⟩ := h₅ i
    exact GlobalTheory.IntegralExpansion.main hL.1 V D A G U k hk s (f i) hs
  choose σ hσ using ex
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨a, ha⟩ := AdaptedSpan.exists_comb hL.1.globalFns U hk σ cls f h₂ h₃ hσ h₅ h₆ h₇ (toGen U.toUnifPre k s)
  obtain ⟨d, b, hd, hb⟩ := exists_denom a
  have e : (d • (show SecG U.toUnifPre k from s)) = ∑ i, b i • σ i := toGen_injective U.toUnifPre k (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smulₛₗ, map_sum, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul, hb])
  refine GlobalTheory.SaturatedSections.existsUnique_comb
    (A := fun j => Γ(G.left, (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))).U j))
    (fun j => GlobalTheory.SaturatedSections.cst G.hom _) hϖ
    (fun j x hx => GlobalTheory.SaturatedSections.eq_zero_of_cst_mul G.hom _ hϖ.ne_zero x hx) (fun i j => LB.Sec.f (σ i) j)
    (fun c y hy => mem_maximalIdeal hL.2.2.2.1.weightIndep U.toUnifPre σ cls f (fun i => hσ i 0)
      (fun i i₀ h => SecOver.ext _ _ fun j => h₆ i (cls i₀) (fun m hm => h (h₂ i₀ i ⟨m, hm⟩).symm) j) h₇ c
      fun j => ?_) s.f d b hd fun j => ?_
  · refine (GlobalTheory.ThickDiv.app_eq_zero_iff hϖ G 0 _ _).2 ⟨y j, ?_⟩
    rw [zero_add, pow_one]
    exact (chart_sum c σ j).trans (hy j).symm
  · exact (congrArg (fun t : SecG U.toUnifPre k => LB.Sec.f t j) e).trans (chart_sum b σ j)

end GlobalTheory.OneBasis.ModelBasis
end
end

