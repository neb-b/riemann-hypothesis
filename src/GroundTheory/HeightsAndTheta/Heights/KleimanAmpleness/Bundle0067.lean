module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MIdealOverOneHeightslock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

section Block

variable {F : Type} [Field F] {K : Type} {ι : K → Type} {L : Type} [Field L] [Algebra F L]

theorem comap_mIdealOver_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    (mIdealOver F y).comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) := by
  have h1 : (mConeMapOver F y).comp (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      ((Polynomial.aeval (X k₀ : MvPolynomial K L)).restrictScalars F).comp
        (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have h2 : ∀ q : Polynomial L,
      aeval (fun _ : K => (Polynomial.X : Polynomial L)) (Polynomial.aeval (X k₀ : MvPolynomial K L) q) = q :=
    fun q => by rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver F y (rename _ f) = 0 ↔ _
  have h := AlgHom.congr_fun h1 f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [← h2 (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

theorem mIdealOver_oneBlock_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      baseComap F k₀ e (mIdealOver F y) := by
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := L) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  ext f
  rw [baseComap, Ideal.mem_comap]
  change mConeMapOver F _ f = 0 ↔ mConeMapOver F y (rename _ f) = 0
  have h := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact rename_injective _ (fun a b _ => Subsingleton.elim a b) (h0.trans (map_zero _).symm)

end Block

theorem CurveNumModel.proof (hMP : ModelPoint.Statement) (hRR : RealiseRestrict.Statement)
    (hIR : Kleiman.InterNumRestrict.Statement.{0, 0}) (hNM : NumModel.Statement) (hMC : ModelCurves.Statement) :
    CurveNumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hm Q β hQ W hW hle hrel
  classical
  have := hW.isPrime
  have hWy : mIdealOver F (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := F), hWy]
  have hy' : ∀ k, ∃ i, genPtOf W ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hW.relevant k
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hleW : mIdealOver F y ≤ mIdealOver F (genPtOf W) := hWy.symm ▸ hle
  have hm' := hMP F K ι Ω y k₀ hm _ (genPtOf W) hy' hleW
  have hxy : ∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0 := fun i h h0 => by
    rw [hx] at h0
    exact h ((hzero ⟨k₀, e.symm i⟩).mpr (hle ((X_mem_mIdealOver_iff y ⟨k₀, e.symm i⟩).mpr h0)))
  obtain ⟨Q', r, hR, hQ'⟩ := hRR F K ι Ω y k₀ N e x hx hm Q β hQ _ (genPtOf W) hm' hleW hxy
  have hpp : Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) =
      W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) := by
    rw [← comap_mIdealOver_block, hWy]
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)) 1 := by
    refine (isSubvar_iff_relDim _ 1).mpr ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hy' k₀
      exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
    · rw [mIdealOver_oneBlock_block, hWy]
      exact ((hMC F K ι Ω y k₀ N e x hx hm 1).1 W hW hle hrel).2.2
  have hxx : Kleiman.primeOf (S := F) x ≤
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) := by
    rw [hx, ← comap_mIdealOver_block, ← comap_mIdealOver_block]
    exact Ideal.comap_mono hleW
  have h1 := hIR F Ω N x _ _ hxy hxx _ 1 hsub ![Q] ![Q'] (fun _ => r) (fun i => by fin_cases i; exact hR)
  have h2 := hNM F K ι _ (genPtOf W) k₀ N e _ rfl hm' 1 ![Q'] ![β] (fun i => by fin_cases i; exact hQ') hsub
  rw [hWy] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1, hpp]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotPartEqGradedPiece
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc cechZc cechBc cechCc locPart quotPart Cell cellMon)

noncomputable section

theorem quotPart_eq_gradedPiece {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (hm : ∀ k, 0 ≤ m k) :
    quotPart F V m = NumbersDVR.gradedPiece V (fun k => (m k).toNat) := by
  have hset : {p : MvPolynomial (Σ k, ι k) F | (∀ k, 0 ≤ m k) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p (fun k => (m k).toNat)} =
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) (fun k => (m k).toNat) : Set _) := by
    ext p
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedHomogeneousSubmodule, hm, implies_true, true_and]
    exact (Bridge.isMultiHomog_iff p _).symm
  rw [quotPart, hset, NumbersDVR.gradedPiece]
  conv_rhs => rw [← Submodule.span_eq (weightedHomogeneousSubmodule F _ _), Submodule.map_span]
  rfl

theorem isMultiHomog_one {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRingOver S ι) 0 := by
  intro d hd k
  classical
  rw [mem_support_iff, coeff_one] at hd
  split_ifs at hd with h
  · subst h
    simp
  · exact absurd rfl hd

theorem MultiSerre.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hI : SectionMapInj.Statement) :
    MultiSerre.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hV' : IsMultiHomogIdeal V := (Bridge.isMultiHomogIdeal_iff V).mp hV
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.IsMGraded F ι (quotPart F V) :=
    HilbertSamuel.QuotPartGraded.proof F K ι V hV'
  obtain ⟨-, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩, -⟩ :=
    hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  obtain ⟨c₃, h₃⟩ := hI F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  filter_upwards [eventually_ge_atTop (fun _ : K => max (max c₁ c₂) (max c₃ 0))] with m hm
  have hk : ∀ k, max (max c₁ c₂) (max c₃ 0) ≤ m k := fun k => hm k
  refine ⟨fun i hi => h₁ m i hi fun k => le_trans (by omega) (hk k), ?_⟩

  let Z := cechZc ι (quotPart F V) m 0
  have hmem : ∀ x ∈ quotPart F V m, (fun _ => LocalizedModule.mk x 1 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechC F ι
      (MvPolynomial (Σ k, ι k) F ⧸ V) 0) ∈ Z := by
    intro x hx
    refine HilbertSamuel.GenTwistGenerated.mem_cechZc_zero (fun J => ?_)
      (HilbertSamuel.GenTwistGenerated.cechD_const x)
    refine Submodule.subset_span ⟨x, 1, 0, isMultiHomog_one, ?_, rfl⟩
    convert hx using 2
    ext k
    simp
  let φ : quotPart F V m →ₗ[F] Z :=
    { toFun := fun x => ⟨fun _ => LocalizedModule.mk x.1 1, hmem x.1 x.2⟩
      map_add' := fun x y => by
        ext I
        simp
      map_smul' := fun r x => by
        ext I
        simp [LocalizedModule.smul'_mk] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hsub : x.1 - y.1 = 0 := by
      refine h₃ m (fun k => le_trans (by omega) (hk k)) _ (Submodule.sub_mem _ x.2 y.2) fun I => ?_
      have h := congrFun (congrArg Subtype.val hxy) I
      change LocalizedModule.mk x.1 1 = LocalizedModule.mk y.1 1 at h
      change LocalizedModule.mkLinearMap (cellMon F I.1) _ (x.1 - y.1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hzx⟩ := h₂ m (fun k => le_trans (by omega) (hk k)) z hz
    exact ⟨⟨x, hx⟩, Subtype.ext (funext fun I => (hzx I).symm)⟩
  have hbot : (cechBc ι (quotPart F V) m 0).comap (cechZc ι (quotPart F V) m 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  have e2 : cechHc ι (quotPart F V) m 0 ≃ₗ[F] Z := Submodule.quotEquivOfEqBot _ hbot
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (by omega) (hk k)
  rw [e2.finrank_eq, ← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, NumbersDVR.hilbFn, if_pos hm0,
    quotPart_eq_gradedPiece V m hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistMulTwistTwistSys
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem twistMul_twist_twistSys {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a : ℕ) (m c : ℤ) :
    (twistMul M a m).twist (twistSys S x c) = twistMul M a (m + c) := by
  rw [twistMul, twistMul, SubSystem.twist_assoc, twistSys_twist_eq_add]

theorem ModelVeryAmpleEq.proof (hVA : VeryAmpleEq.Statement) (hMS : ModelMulSecs.Statement)
    (hCh : ModelChangeVeryAmple.Statement) : ModelVeryAmpleEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ a m _
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul Q a m
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (L.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen L n g := hg
  have hmod' := GraphModel.full F N Ω _ L n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver L n g hgen
  have hH : ∀ c : ℤ, (L.twist (twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro c
    rw [hL, twistMul_twist_twistSys, hMS F K ι Ω y k₀ N e hmod β Q hQ a (m + c), add_smul, add_assoc]
  rw [← hL, hVA F N Ω _ L n (r + 1) g hgen]
  exact hCh F Ω N (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) K ι y k₀ e hmod' hmod rfl
    (graphDeg n) (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (fun c => (hsec c).symm.trans (hH c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

