module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleOfTwistedBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantCondition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DiagCoord

theorem exists_linearIndependent_of_iSupIndep {k V I T : Type} [Field k] [AddCommGroup V] [Module k V] [Finite I]
    (W : T → Submodule k V) (hW : iSupIndep W) (ty : I → T)
    (b : ∀ τ, Nonempty (Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ))) :
    ∃ v : I → V, LinearIndependent k v ∧ ∀ i, v i ∈ W (ty i) := by
  classical
  let B : ∀ τ, Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ) := fun τ => (b τ).some
  let e : ∀ τ, {i // ty i = τ} ≃ Fin (Nat.card {i // ty i = τ}) := fun τ => Finite.equivFin _
  let f : ∀ τ, {i // ty i = τ} → V := fun τ j => ((B τ (e τ j) : W τ) : V)
  have hmem : ∀ τ j, f τ j ∈ W τ := fun τ j => (B τ (e τ j)).2
  have hspan : ∀ τ, Submodule.span k (Set.range (f τ)) ≤ W τ := by
    intro τ
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem τ j
  have hsig : LinearIndependent k (fun p : Σ τ, {i // ty i = τ} => f p.1 p.2) := by
    refine linearIndependent_iUnion_finite (fun τ => ?_) (fun τ t _ hτ => ?_)
    · exact ((B τ).linearIndependent.map' (W τ).subtype (Submodule.ker_subtype _)).comp
        (e τ) (e τ).injective
    · exact (hW.disjoint_biSup hτ).mono (hspan τ) (iSup₂_mono fun σ _ => hspan σ)
  let s : I → Σ τ, {i // ty i = τ} := fun i => ⟨ty i, ⟨i, rfl⟩⟩
  have hs : Function.Injective s := fun i j h => congrArg (fun p : Σ τ, {i // ty i = τ} => (p.2 : I)) h
  exact ⟨fun i => f (ty i) ⟨i, rfl⟩, hsig.comp s hs, fun i => hmem (ty i) ⟨i, rfl⟩⟩


open GlobalTheory.Serre ReciprocityTheory.ChartRestriction.G.Chart in
theorem exists_diff_linear {O : Type} [CommRing O] {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (act : OAct O A) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ d : Serre.Lie act →ₗ[ℂ] (Fin g → ℂ), Function.Injective d ∧ ∀ v, u.IsDiff (d v) v.hom := by
  classical
  let dd : Serre.Lie act → (Fin g → ℂ) := fun v => (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose
  have hdd : ∀ v : Serre.Lie act, u.IsDiff (dd v) v.hom := fun v =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose_spec
  have huniq : ∀ (v : Serre.Lie act) (w : Fin g → ℂ), u.IsDiff w v.hom → dd v = w := fun v w hw =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).unique (hdd v) hw
  have hcomb : ∀ (n : ℕ) (r : Fin n → ℂ) (vs : Fin n → Serre.Lie act),
      u.IsDiff (∑ i, r i • dd (vs i)) (∑ i, r i • vs i).hom := fun n r vs =>
    GlobalTheory.UnifDifferential.isDiff_of_isLieComb A L g n u (fun i => dd (vs i)) (fun i => (vs i).hom) r _
      (fun i => GlobalTheory.Serre.Lie.isTangent (vs i)) (fun i => hdd (vs i))
      ((GlobalTheory.Serre.Lie.isLieComb_iff r vs _).2 rfl)
  have hadd : ∀ v w : Serre.Lie act, dd (v + w) = dd v + dd w := by
    intro v w
    apply huniq
    have h2 := hcomb 2 ![1, 1] ![v, w]
    simpa [Fin.sum_univ_two] using h2
  have hsmul : ∀ (c : ℂ) (v : Serre.Lie act), dd (c • v) = c • dd v := by
    intro c v
    apply huniq
    have h1 := hcomb 1 ![c] ![v]
    simpa using h1
  refine ⟨{ toFun := dd, map_add' := hadd, map_smul' := hsmul }, ?_, hdd⟩
  intro v w hvw
  apply GlobalTheory.Serre.Lie.ext
  have hw : u.IsDiff (dd v) w.hom := by
    have := hdd w
    have hvw' : dd v = dd w := hvw
    rwa [← hvw'] at this
  exact (h₂ (dd v)).unique ⟨GlobalTheory.Serre.Lie.isTangent v, hdd v⟩ ⟨GlobalTheory.Serre.Lie.isTangent w, hw⟩

end GlobalTheory.DiagCoord


open GlobalTheory.DiagCoord GlobalTheory.Serre in
theorem GlobalTheory.exists_diagonal_coordinates_of_detCond :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  intro _ _ _ _ E _ _ _ H D P u Hm χ act ty _ hty hdet
  unfold DetCond at hdet
  unfold IsTypeFn at hty
  have : IsCommMonObj P.A := Out.PolAV.isCommMonObj P
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u P.smoothDim
  obtain ⟨d, hdinj, hdd⟩ := exists_diff_linear u act h₁ h₂
  let ty' : Fin P.g → (𝓞 E →+* ℂ) := fun i => (ty i).comp (algebraMap (𝓞 E) E)
  have hinj : ∀ τ : 𝓞 E →+* ℂ, Function.Injective τ := by
    intro τ
    refine (RingHom.injective_iff_ker_eq_bot τ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
    ext n
    simp [RingHom.mem_ker]
  have hcard : ∀ τ : 𝓞 E →+* ℂ, ∃ σ : E →+* ℂ, σ (H.rt : E) = τ H.rt ∧
      Nat.card {i // ty' i = τ} = Nat.card {i // ty i = σ} := by
    intro τ
    refine ⟨IsFractionRing.lift (hinj τ), IsFractionRing.lift_algebraMap (hinj τ) H.rt,
      Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun hi => ?_, fun hi => ?_⟩)⟩
    · refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
      exact congrArg (fun f : 𝓞 E →+* ℂ => f x) hi
    · refine RingHom.ext fun x => ?_
      show ty i (algebraMap (𝓞 E) E x) = τ x
      rw [hi]
      exact IsFractionRing.lift_algebraMap (hinj τ) x
  have hb : ∀ τ : 𝓞 E →+* ℂ,
      Nonempty (Module.Basis (Fin (Nat.card {i // ty' i = τ})) ℂ (GlobalTheory.Serre.Lie.eig act τ)) := by
    intro τ
    obtain ⟨σ, hσ, hc⟩ := hcard τ
    refine (GlobalTheory.Serre.Lie.lieMult_id_iff act τ _).1 ?_
    rw [hc]
    by_cases hτ : τ H.rt = H.rt0
    · rw [(hty σ).1 (hσ.trans hτ)]
      exact (hdet τ).1 hτ
    · rw [(hty σ).2 (fun h => hτ (hσ.symm.trans h))]
      exact (hdet τ).2 hτ
  obtain ⟨v, hvli, hvmem⟩ :=
    exists_linearIndependent_of_iSupIndep (GlobalTheory.Serre.Lie.eig act) (GlobalTheory.Serre.Lie.iSupIndep_eig act) ty' hb
  choose F hF using fun a : 𝓞 E =>
    GlobalTheory.exists_linear_lift_of_isMonHom_polAV P P P.L P.L u u (act.act a) (act.hom a)
  have key : ∀ (a : 𝓞 E) (i : Fin P.g), F a (d (v i)) = ty i (a : E) • d (v i) := by
    intro a i
    have := act.hom a
    have e1 := GlobalTheory.HomLinear.isDiff_comp u u (act.act a) (F a) (hF a)
      (GlobalTheory.Serre.Lie.isTangent (v i)) (hdd (v i))
    have hv : a • v i = ty' i a • v i := (GlobalTheory.Serre.Lie.mem_eig_iff.1 (hvmem i)) a
    have e2 : (ty' i a • v i).hom = (v i).hom ≫ act.act a := by
      rw [← hv, GlobalTheory.Serre.Lie.hom_act_smul]
    rw [← e2] at e1
    have e3 := hdd (ty' i a • v i)
    rw [map_smul] at e3
    exact (h₁ _ (GlobalTheory.Serre.Lie.isTangent _)).unique e1 e3
  have hli : LinearIndependent ℂ (d ∘ v) := hvli.map' d (LinearMap.ker_eq_bot.2 hdinj)
  let B : Module.Basis (Fin P.g) ℂ (Fin P.g → ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank' (d ∘ v) hli (by simp)
  have hB : ∀ i, B i = d (v i) := fun i => by simp [B]
  refine ⟨B.equivFun.symm, fun a z => ?_⟩
  rw [← hF a]
  refine congrArg u.ex ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hB, key, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleLinearisation
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.ThetaLin

open GlobalTheory.CommPairing GlobalTheory.ThetaSplit ReciprocityTheory.ChartRestriction.G.H1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    Out.translT A (x * y) = Out.translT A x ≫ Out.translT A y := by
  conv_rhs => rw [Out.translT, CommutatorPairing.lift_translT]
  rw [Out.translT]
  congr 1
  show (fst T A ≫ (x * y)) * snd T A = (fst T A ≫ y) * ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, _root_.mul_assoc, mul_left_comm]

theorem translT_snd {T : Over S} (x : T ⟶ A) :
    (Out.translT A x).left ≫ (snd T A).left = (Out.translPt A x).left := by
  rw [← Over.comp_left, Out.translT, lift_snd]

theorem translT_translPt [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translPt A (x * y)).left := by
  rw [← translT_snd (x * y), translT_mul, Over.comp_left, Category.assoc, translT_snd]

theorem exists_symm_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {C : Type} [CommGroup C] (θ : C → Out.ThetaGrp A L k T)
    (hm : ∀ c c', (θ (c * c')).pt = (θ c).pt * (θ c').pt) (hc : ∀ c c', Out.CommIsOf A L k (θ c) (θ c') 1) :
    ∃ a : C → C → Γ(T.left, ⊤)ˣ, (∀ x y, a x y = a y x) ∧ (∀ x y z, a x y * a (x * y) z = a y z * a x (y * z)) ∧
      ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ (a c c') := by
  have := hA.comm
  let e : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) 1).left
  have he : e ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have ex : ∀ c c', ∃ a : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ a := fun c c' => by
    obtain ⟨a, ha⟩ := CommutatorPairing.exists_ratio hL (fun U _ g => by
        refine Eq.trans ?_ (Fintype.prod_sum_type _).symm
        simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
        show g (snd T A).left ^ k * g (Out.translPt A (θ (c * c')).pt).left ^ (-k) =
          g (snd T A).left ^ k * g (Out.translPt A (θ c).pt).left ^ (-k) *
            (g ((Out.translT A (θ c).pt).left ≫ (snd T A).left) ^ k *
              g ((Out.translT A (θ c).pt).left ≫ (Out.translPt A (θ c').pt).left) ^ (-k))
        rw [translT_snd, translT_translPt, hm]
        simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) (fst T A).left e he (surj_fst hG hA T)
      (θ (c * c')).isGen
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (θ c).isGen
        (DVR.pullGen_isGen _ _ _ _ (θ c').isGen (Out.translT A (θ c).pt).left))
    exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (tval (θ c) r z J * ·) (val_pull hJ _ _ _))))⟩
  choose a ha using ex
  have inj : ∀ u u' : Γ(T.left, ⊤)ˣ, (∀ (y : T.left) (J), Good L y J →
      gm (e ≫ (fst T A).left) y ⊤ u = gm (e ≫ (fst T A).left) y ⊤ u') → u = u' :=
    fun u u' h => unit_ext fun y _ => by
      choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ y)
      rw [← he]; exact h y J hJ
  refine ⟨a, fun c c' => inj _ _ fun y J hJ => ?_, fun c c' c'' => inj _ _ fun y J hJ => ?_, ha⟩
  · have e₁ := ha c c' _ e y J hJ
    have e₂ := ha c' c _ e y J hJ
    have e₃ := (commIsOf_iff hL _ _ _).1 (hc c c') _ e y J hJ
    rw [map_one, _root_.mul_one] at e₃
    rw [e₃] at e₁
    rw [mul_comm c' c, e₁] at e₂
    exact mul_left_cancel e₂
  · have e₁ := ha c c' _ e y J hJ
    have e₂ := ha (c * c') c'' _ e y J hJ
    have e₃ := ha c' c'' _ (e ≫ (Out.translT A (θ c).pt).left) y J hJ
    have e₄ := ha c (c' * c'') _ e y J hJ
    rw [_root_.mul_assoc c] at e₂
    rw [Category.assoc, Category.assoc, translT_fst, ← Over.comp_left _ _ _ (Out.translT A (θ c).pt), ← translT_mul, ← hm] at e₃
    rw [map_mul, map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e₁
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    have a₄ := congrArg Additive.ofMul e₄
    simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
    linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂

theorem exists_linearisation {L : LB A.left} (hL : L.IsLB) (n : ℕ) {T : Over S} {C : Type} [CommGroup C]
    (θ : C → Out.ThetaGrp A L n T) (a : C → C → Γ(T.left, ⊤)ˣ)
    (ha : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        tval (θ (c * c')) r z J = tval (θ c) r z J * tval (θ c') (r ≫ (Out.translT A (θ c).pt).left) z J *
          gm (r ≫ (fst T A).left) z ⊤ (a c c'))
    {S' : Scheme.{0}} {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (τ : S' ⟶ T.left) (hτ : τ ≫ T.hom = f) (i' : C →* (𝟙_ (Over S') ⟶ A'))
    (hi : ∀ c, τ ≫ (θ c).pt.left = (i' c).left ≫ φ) (b : C → Γ(S', ⊤)ˣ)
    (hb : ∀ c c', Units.map τ.appTop.hom.toMonoidHom (a c c') * b (c * c') = b c * b c') :
    ∃ u : ∀ c, LB.Gen (LB.LinComb (lbPow L' n) (K := Fin 2) ![𝟙 A'.left, transl (i' c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L' n) _ _ _ _ (u (c * c'))
        (LB.mulGen (lbPow L' n) _ _ _ _ (u c) (LB.pullGen (lbPow L' n) _ _ (u c') (transl (i' c)))) := by
  obtain ⟨w, hw⟩ := hw
  have hτ' : (τ : (𝟙_ (Over S')).left ⟶ T.left) ≫ T.hom = (𝟙_ (Over S')).hom ≫ f :=
    hτ.trans (Category.id_comp _).symm
  choose θ' hθ' hR using fun c => WeilPull.exists_rel_down hp (T := 𝟙_ (Over S')) τ hτ' hL hL' w hw (i' c) (θ c) (hi c)
  have key : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S') ⊗ A').left) (z : Z) (J), Good L' z J →
      tval (θ' (c * c')) r z J = tval (θ' c) r z J * tval (θ' c') (r ≫ (Out.translT A' (i' c)).left) z J *
        gm ((r ≫ (fst _ A').left) ≫ τ) z ⊤ (a c c') := fun c c' Z r z J hJ => by
    choose J₀ hJ₀ using fun ψ : Z ⟶ A.left => exists_chart hL (ψ z)
    have e := ha c c' Z (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) z J₀ hJ₀
    have t : (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) ≫ (Out.translT A (θ c).pt).left =
        (r ≫ (Out.translT A' (i' c)).left) ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left := by
      rw [Category.assoc, Category.assoc, psi_transl hp (T := 𝟙_ (Over S')) τ hτ' _ _ (hi c)]
    have g : (r ≫ (psiO hp (T := 𝟙_ (Over S')) τ hτ').left) ≫ (fst T A).left = (r ≫ (fst _ A').left) ≫ τ := by
      rw [Category.assoc, psi_fst, Category.assoc]
    have s : (r ≫ (Out.translT A' (i' c)).left) ≫ (snd _ A').left = r ≫ (Out.translPt A' (i' c)).left := by
      rw [Category.assoc, translT_snd]
    have q : (r ≫ (Out.translT A' (i' c)).left) ≫ (Out.translPt A' (i' c')).left =
        r ≫ (Out.translPt A' (i' (c * c'))).left := by
      rw [Category.assoc, translT_translPt, map_mul]
    rw [t, g, hR _ Z _ z J₀ J hJ₀ hJ, hR _ Z _ z J₀ J hJ₀ hJ, hR _ Z _ z J₀ J hJ₀ hJ, hθ', hθ', hθ', s, q] at e
    simp only [zpow_neg] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  choose v hv ev using fun c => exists_gen_theta hL' (θ' c) (hθ' c)
  choose u hu eu using fun c => exists_gen_lbPow n (ε := ![1, -1]) (fun k => by fin_cases k <;> simp) (v c) (hv c)
    (pullU A'.hom ⊤ (b c))
  refine ⟨u, hu, fun c c' => corr_of_val (DVR.linComb_isLB L' hL' _ _) fun y J hJ => ?_⟩
  have hJ' : Good L' y (fun χ => J χ PUnit.unit) := fun χ => Set.mem_iInter.1 (hJ χ) PUnit.unit
  have g : ∀ (r : A'.left ⟶ A'.left) (a : Γ(S', ⊤)ˣ), gm r y ⊤ (pullU A'.hom ⊤ a) = gm (r ≫ A'.hom) y ⊤ a :=
    fun r a => gm_pull r A'.hom y ⊤ trivial a
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg (val (u c) (𝟙 _) y J * ·) (val_pull hJ _ _ _))).symm
  rw [eu _ _ _ y J hJ, eu _ _ _ y J hJ, eu _ _ _ y J hJ, g, g, g, Category.assoc, transl_hom,
    ev _ _ _ y _ hJ', ev _ _ _ y _ hJ', ev _ _ _ y _ hJ', key c c' _ _ y _ hJ']
  have f₁ : (𝟙 A'.left ≫ (lift (toUnit A') (𝟙 A')).left) ≫ (fst _ A').left = 𝟙 A'.left ≫ A'.hom := by
    rw [Category.assoc, ← Over.comp_left, lift_fst]; rfl
  have f₂ : (𝟙 A'.left ≫ (lift (toUnit A') (𝟙 A')).left) ≫ (Out.translT A' (i' c)).left =
      (𝟙 A'.left ≫ transl (i' c)) ≫ (lift (toUnit A') (𝟙 A')).left := by
    rw [Category.assoc, Category.assoc, transl_lift]
  have f₃ := gm_pull (𝟙 A'.left ≫ A'.hom) τ y ⊤ trivial (a c c')
  have f₄ := congrArg (gm (𝟙 A'.left ≫ A'.hom) y ⊤) (hb c c')
  rw [map_mul, map_mul] at f₄
  rw [f₁, f₂, _root_.mul_assoc]
  exact (congrArg (_ * ·) ((congrArg (· * _) f₃.symm).trans f₄)).trans (_root_.mul_mul_mul_comm _ _ _ _)

theorem exists_lifts_away {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {C : Type} [Finite C] (x : C → (𝟙_ (Over (Sp R)) ⟶ A)) (q : PrimeSpectrum R)
    (hW : ∀ c, Out.WeilIs A L k (x c) (x c) 1) :
    ∃ r : R, r ∉ q.asIdeal ∧ ∀ c, ∃ θ : Out.ThetaGrp A L k (Over.mk (spMap (algebraMap R (Localization.Away r)))),
      θ.pt = toUnit _ ≫ x c := by
  choose V hV hθ using fun c => hW c q
  have ho : IsOpen (X := PrimeSpectrum R) (⋂ c, (V c).1) := isOpen_iInter_of_finite fun c => (V c).2
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hV) ho
  refine ⟨r, hr, fun c => ?_⟩
  obtain ⟨⟨θ, -, e, -⟩, -⟩ := hθ c
  have hsub : Set.range (spMap (algebraMap R (Localization.Away r))) ⊆ Set.range (V c).ι := by
    rintro _ ⟨p, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) p ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact ⟨p, rfl⟩
    exact ⟨⟨_, Set.mem_iInter.1 (hle this) c⟩, rfl⟩
  let h : Over.mk (spMap (algebraMap R (Localization.Away r))) ⟶ Out.overRes (V c) :=
    Over.homMk (IsOpenImmersion.lift (V c).ι _ hsub) (by
      show IsOpenImmersion.lift (V c).ι _ hsub ≫ (V c).ι ≫ 𝟙 _ = _
      rw [Category.comp_id, IsOpenImmersion.lift_fac]; rfl)
  obtain ⟨θ', e', -⟩ := exists_pull hL h θ
  exact ⟨θ', by rw [e', e, ← Category.assoc, toUnit_unique (h ≫ _) (toUnit _)]⟩

end GlobalTheory.ThetaLin

namespace GlobalTheory


open ThetaLin in
theorem exists_etale_linearisation : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over (Sp R)) ⟶ P.A)) (q : PrimeSpectrum R), IsUnit (n : R) → 0 < n → (∀ c : C, c ^ n = 1) → (∀ c c', Out.WeilIs P.A P.L n (i c) (i c') 1) → ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Algebra.Etale R R' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap R R')) ∧ ∀ (A' : Over (Sp R')) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ P.A.left) (L' : LB A'.left) (i' : C →* (𝟙_ (Over (Sp R')) ⟶ A')), IsGrpPullback A' P.A (spMap (algebraMap R R')) φ → L'.IsLB → LBIso L' (P.L.pull φ) → (∀ c, (i' c).left ≫ φ = spMap (algebraMap R R') ≫ (i c).left) → ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow L' n) (K := Fin 2) ![𝟙 A'.left, ((toUnit A' ≫ i' c) * 𝟙 A').left] ![1, -1]), (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L' n) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow L' n) _ _ _ _ (u c) (LB.pullGen (lbPow L' n) _ _ (u c') ((toUnit A' ≫ i' c) * 𝟙 A').left)) := by
  intro R _ P n C _ _ i q hnR hn htor hW
  have hG := GlobalTheory.globalFns_holds
  have := P.isAb.comm
  obtain ⟨r, hr, hθ⟩ := exists_lifts_away P.isLB (fun c => i c) q (fun c => hW c c)
  choose θ hθ using hθ
  let R₁ := Localization.Away r
  obtain ⟨a, hs, hc, ha⟩ := exists_symm_cocycle hG P.isAb P.isLB θ
    (fun c c' => by rw [hθ, hθ, hθ, map_mul, MonObj.comp_mul]) (fun c c' => by
      refine (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB _ _ _).1 ?_
      have H := CommPairing.weilIs_pull hG P.isAb P.isLB (toUnit (Over.mk (spMap (algebraMap R R₁)))) (hW c c')
      rw [map_one] at H
      rw [hθ, hθ]; exact H)
  let e₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  let E₁ : Γ(Sp R₁, ⊤)ˣ →* R₁ˣ := Units.map e₁.toRingHom.toMonoidHom
  obtain ⟨R', _, _, het, -, hff, b, hb⟩ := GlobalTheory.CocycleSplit.exists_etale_splitting R₁ n C (fun x y => E₁ (a x y))
    (by simpa using hnR.map (algebraMap R R₁)) hn htor (fun x y => congrArg E₁ (hs x y))
    (fun x y z => (map_mul E₁ _ _).symm.trans ((congrArg E₁ (hc x y z)).trans (map_mul E₁ _ _)))
  letI : Algebra R R' := ((algebraMap R₁ R').comp (algebraMap R R₁)).toAlgebra
  have : IsScalarTower R R₁ R' := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R R₁ := Algebra.Etale.of_isLocalizationAway r
  refine ⟨R', inferInstance, inferInstance, Algebra.Etale.comp R R₁ R', ?_, ?_⟩
  · have h₁ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R R₁)) := by
      rw [PrimeSpectrum.localization_away_comap_range R₁ r]; exact hr
    obtain ⟨p, rfl⟩ := h₁
    obtain ⟨p', rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R₁) (B := R') p
    exact ⟨p', rfl⟩
  · intro A' _ _ φ L' i' hp hL' hw hi
    have hτ : spMap (algebraMap R₁ R') ≫ spMap (algebraMap R R₁) = spMap (algebraMap R R') := by
      rw [← Spec.map_comp]; rfl
    let e' : Γ(Sp R', ⊤) ≃+* R' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
    refine exists_linearisation P.isLB n θ a ha hp hL' hw (spMap (algebraMap R₁ R')) hτ i' (fun c => ?_)
      (fun c => Units.map e'.symm.toRingHom.toMonoidHom (b c)) (fun c c' => ?_)
    · rw [hθ, hi, ← hτ, Category.assoc]; rfl
    · rw [← map_mul, ← hb, map_mul]
      congr 1
      apply Units.ext
      apply e'.injective
      have := congrArg (fun g => g.hom (a c c').val)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R₁ R')))
      exact this.trans (e'.apply_symm_apply _).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem exists_gen_of_eq {X Y : Scheme.{0}} (L : LB X) {p q : Y ⟶ X} (h : q = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => q) (fun _ => n)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι),
        gm r z (LB.wchart L (fun _ => q) j) (b.s j) = gm r z (LB.wchart L (fun _ => p) j) (a.s j)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  subst h
  exact ⟨a, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem exists_mapsAt_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L (J := PUnit) (fun _ => F) (isoPullId (idIso L) hF) p n a b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  obtain ⟨b, hb, hv⟩ := exists_gen_of_eq L (q := p ≫ F) (p := p) (by rw [hF, Category.comp_id]) n a
  refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, hv⟩
  have hL : p y ∈ L.U jL := hy.2
  have hN : p y ∈ L.U (jN PUnit.unit) := by
    have := mem_pull.1 hy.1
    rw [hF] at this
    exact this
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) jN := Set.mem_iInter.2 fun _ => hN
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) (fun _ => jL) := Set.mem_iInter.2 fun _ => hL
  refine (gm_res _ y _ hy _).trans ((hb _ _ y jN).trans ((gen_trans ha (𝟙 Y) y m₁ m₂).trans ?_))
  refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (gm_res _ y _ hy _)))
  rw [trF, Fintype.prod_unique]
  refine congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans ?_)
  exact gw_isoPullId (idIso L) hF (𝟙 Y ≫ p) y (jN PUnit.unit) jL hN hL

theorem exists_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens), genericPoint (Sp R) ∈ W → Nonempty (PsiOn D W) → ∃ hD : IsPullDeg (RingHom.id R) D D, IsIdPull hD := by
  rintro R _ _ D W hW ⟨ψ⟩
  have hs := specOf_id R
  have mR : IsMonHom (Iso.refl D.P.A).hom := by show IsMonHom (𝟙 _); infer_instance
  have gp : IsGrpPullback D.P.A D.P.A (specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr hs.symm rfl
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))
  have hF : e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := he
  have hz : eSec D.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := by
    rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
  have hgen : ∀ z : Sp (FractionRing R), jK R z ∈ W := by
    intro z
    have : jK R z = genericPoint (Sp R) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
      have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.isPrime
      rw [hz0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
    rw [this]; exact hW
  have hr : Set.range (𝟙 (Sp (FractionRing R)) : _ ⟶ _) ⊆ Set.range (jK R ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hgen z
  let l := IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) hr
  have hl : l ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ e := e, e_hom := me, w := isoPullId (idIso D.P.L) hF
            w_gen := (isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF)
            he := hz
            w_rig := isoPullId_maps (idIso_maps (⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ : RigLB D.P.A)) hF hs hz
            xe := AddEquiv.refl _
            c_pr := fun x => by rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
            W := W, psiW := ψ, g := l ≫ jK R ∣_ W
            g_comm := by
              rw [hs, Category.comp_id]
              exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (morphismRestrict_ι (jK R) W)).trans
                ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hl).trans (Category.id_comp _))))
            psi_pr := fun x => ?_ }, fun _ => rfl, hF, fun Y f y j k hj hk => ?_⟩
  · obtain ⟨b, hb, hv⟩ := exists_mapsAt_id hF (D.xK x) (-1) (D.psi x) (D.psi_gen x)
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have c := val_corr hJ (ψ.psi_eq x) l
    have c₁ := val_pull hJ (ψ.psi x) (jK R ∣_ W) l
    have c₂ := val_pull hJ (D.psi x) (jK R ⁻¹ᵁ W).ι l
    have c₃ := val_pull hJ (ψ.psi x) (l ≫ jK R ∣_ W) (𝟙 _)
    refine (hv _ _ y J).trans (Eq.trans ?_ c₃.symm)
    refine (congrArg (fun r => val (D.psi x) r y J) hl).symm.trans (c₂.symm.trans (c.symm.trans (c₁.trans ?_)))
    exact congrArg (fun r => val (ψ.psi x) r y J) (Category.id_comp _).symm
  · exact gw_isoPullId (idIso D.P.L) hF f y j k hj hk

end GlobalTheory.TorsionFormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.weilIs_iff_of_isGrpPullback_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] [IsCommMonObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) :=
  GlobalTheory.weilIs_grpPullback_of_comm
end

