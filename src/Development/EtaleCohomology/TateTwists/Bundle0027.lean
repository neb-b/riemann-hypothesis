module

public import Development.EtaleCohomology.TateTwists.Bundle0017
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
public import Development.EtaleCohomology.TateTwists.Bundle0018
public import Development.EtaleCohomology.TateTwists.Bundle0019

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem ulift_smul_eq {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (x : M) : r • x = r.down.val • x := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    apply ULift.ext; simp only [ULift.down_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  rw [Nat.cast_smul_eq_nsmul]

theorem q_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (c : ℕ) (hc : q ∣ c) (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simpa using (ZMod.natCast_eq_zero_iff c q).2 hc
  rw [this, zero_smul]

theorem exists_functional {q : ℕ} [NeZero q] {M : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (g : M) (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) :
    ∃ F : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), F g = 1 := by
  letI : Module (ZMod q) M :=
    Module.compHom M (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom
  have hsm : ∀ (r : ZMod q) (x : M), r • x = (ULift.up r : ULift.{1} (ZMod q)) • x := fun r x => rfl
  let f : ZMod q →ₗ[ZMod q] M := LinearMap.toSpanSingleton (ZMod q) M g
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : r.val • g = 0 := by
      have h2 : (ULift.up r : ULift.{1} (ZMod q)) • g = 0 := hr
      have h4 := ulift_smul_eq (M := M) (ULift.up r : ULift.{1} (ZMod q)) g
      exact h4.symm.trans h2
    have h3 := hg _ h1
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_zero_iff _ _).2 h3
  obtain ⟨h, hh⟩ := (KStar.Selmer.zmod_baer (N := q)).extension_property f hf LinearMap.id
  refine ⟨{ toFun := fun x => ULift.up (h x), map_add' := fun x y => by ext; simp,
             map_smul' := fun r x => ?_ }, ?_⟩
  · change ULift.up (h (r.down • x)) = r • ULift.up (h x)
    rw [h.map_smul]
    ext; simp [smul_eq_mul]
  · have := LinearMap.congr_fun hh 1
    simp only [LinearMap.comp_apply, f, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply] at this
    ext; simpa using this

theorem dvd_of_tmul {q : ℕ} [NeZero q] {M N : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N] (g : M) (g' : N)
    (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) (hg' : ∀ c : ℕ, c • g' = 0 → q ∣ c) (c : ℕ)
    (h : c • (g ⊗ₜ[ULift.{1} (ZMod q)] g') = 0) : q ∣ c := by
  obtain ⟨F, hF⟩ := exists_functional g hg
  obtain ⟨F', hF'⟩ := exists_functional g' hg'
  let L := TensorProduct.lift ((LinearMap.mul (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))).compl₂ F' ∘ₗ F)
  have := congrArg L h
  simp only [map_nsmul, L, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.mul_apply', hF, hF', mul_one, map_zero, nsmul_eq_mul] at this
  have h2 := congrArg ULift.down this
  simp at h2
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

end LateralTheory.EtaleFoundations.GenIsoInj

namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem sm_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := map_nsmul _ _ _
theorem sm_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sr_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _
theorem sr_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sgl_smul_eq_zero {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (c : ℕ) (x : Sec F U)
    (h : c • Sec.map (sglι F) x = 0) : c • x = 0 := by
  let ψ : (sgl F).X 0 ⟶ F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  have hψ : sglι F ≫ ψ = 𝟙 F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  have e : ∀ y : Sec F U, Sec.map ψ (Sec.map (sglι F) y) = y := fun y => by
    rw [TwMulPf.sec_map_comp, hψ, TwMulPf.sec_map_id]
  have h' : Sec.map (sglι F) (c • x) = Sec.map (sglι F) 0 := by
    rw [show Sec.map (sglι F) (c • x) = c • Sec.map (sglι F) x from map_nsmul _ c x, h]
    exact (map_zero _).symm
  have := congrArg (Sec.map ψ) h'
  rwa [e, e] at this

end LateralTheory.EtaleFoundations.GenIsoInj


open LateralTheory.EtaleFoundations.GenIsoInj LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_injective_of_sections_glue (hts : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (hlb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (hsg : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective := by
  classical
  intro q _ i j k T μ hμ hk φ hφ U a ha
  have nt : ∀ (l : ℤ) (W : Scheme.{0}) [Nonempty W] (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
      c • Sec.map (sglι (tw q l)) (twGen l ζ) = 0 → q ∣ c :=
    fun l W _ ζ c h => (hts q l).2.2.1 W ζ c (LateralTheory.EtaleFoundations.GenIsoInj.sgl_smul_eq_zero c _ h)
  refine hlb.2.2.2.2.1 U _ (hlb.2.1 U _ _ ((hts q k).1 U a) ?_)
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact hlb.1 V _ fun W h => by rw [LateralTheory.EtaleFoundations.GenIsoInj.res_comp, h0, LateralTheory.EtaleFoundations.GenIsoInj.sr_zero]
  · have h1 : c • μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ))
        (Sec.map (sglι _) (twGen j ζ)) = 0 := by
      rw [← hφ V ζ, ← LateralTheory.EtaleFoundations.GenIsoInj.sm_nsmul, ← LateralTheory.EtaleFoundations.GenIsoInj.sm_nsmul, ← hc, ← LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, ha, LateralTheory.EtaleFoundations.GenIsoInj.sr_zero, LateralTheory.EtaleFoundations.GenIsoInj.sm_zero]
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V)
        ⟨(0, 0), rfl⟩ (c • (Sec.map (sglι _) (twGen i ζ) ⊗ₜ Sec.map (sglι _) (twGen j ζ)))
    have hx : μ.lift V 0 x = 0 := by
      simp only [x, Pair.lift, DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]
      exact h1
    refine hlb.2.1 V _ _ (hμ.2 V 0 x hx) fun W h hW => ?_
    have hW' : c • (Sec.res h (Sec.map (sglι _) (twGen i ζ)) ⊗ₜ[ULift.{1} (ZMod q)]
        Sec.res h (Sec.map (sglι _) (twGen j ζ))) = 0 := by
      have := congrArg (DirectSum.component (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) W ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) W)
        ⟨(0, 0), rfl⟩) hW
      simpa [x, Tens.res, DirectSum.component.lof_self] using this
    show Sec.res (h ≫ g) a = 0
    rw [LateralTheory.EtaleFoundations.GenIsoInj.res_comp, hc, LateralTheory.EtaleFoundations.GenIsoInj.sr_nsmul]
    by_cases hne : Nonempty W
    · rw [LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, LateralTheory.EtaleFoundations.TwMulPf.sec_res_map, (hts q i).2.2.2.1, (hts q j).2.2.2.1] at hW'
      exact LateralTheory.EtaleFoundations.GenIsoInj.q_smul c (LateralTheory.EtaleFoundations.GenIsoInj.dvd_of_tmul _ _ (nt i W _) (nt j W _) c hW') _
    · have : IsEmpty W := not_nonempty_iff.1 hne
      exact (hsg (ZMod q) (tw q k) W).1 _ _ (hlb.2.2.2.2.2.2 W _)
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorCyclesLocallyLiftOfRowExactAndDescent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

theorem stair_tens_top {R : Type} [CommRing R] {C J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens C J U w) :
    ∃ s : ℤ, ∀ p, s < p.1.1 → x p = 0 := by
  classical
  refine ⟨((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ), fun p hp => ?_⟩
  by_contra h
  have hm : p ∈ DFinsupp.support x := (DFinsupp.mem_support_iff).2 h
  have h1 : p.1.1.toNat ≤ (DFinsupp.support x).sup fun p => p.1.1.toNat := Finset.le_sup (f := fun p => p.1.1.toNat) hm
  have h2 : p.1.1 ≤ (p.1.1.toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((p.1.1.toNat : ℕ) : ℤ) ≤ (((DFinsupp.support x).sup fun p => p.1.1.toNat : ℕ) : ℤ) := by exact_mod_cast h1
  omega

theorem stair_loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem stair_sec_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) (U : Scheme.{0}) (y : Sec F U) : y = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have := congrArg (fun m : F ⟶ F => (m.hom.app (op U)).hom y) h
  simpa using this

theorem stair_tens_low {R : Type} [CommRing R] {C J : Cx R} (a : ℤ) [C.IsStrictlyGE a] {U : Scheme.{0}} {w : ℤ}
    (x : Tens C J U w) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (hp : p.1.1 < a) : x p = 0 := by
  have hz := C.isZero_of_isStrictlyGE a p.1.1 hp
  have key : ∀ y : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U, y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rfl
    | tmul u v => rw [stair_sec_zero hz U u, TensorProduct.zero_tmul]
    | add u v hu hv => rw [hu, hv, add_zero]
  exact key _

theorem stair_fg_zero {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.sc w).X₁ V) :
    Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = 0 := by
  have h1 : Sec.map (T.sc w).g (Sec.map (T.sc w).f z) = ((((T.sc w).f ≫ (T.sc w).g).hom.app (op V)).hom z) := rfl
  rw [h1, (T.sc w).zero]
  rfl

def stair_row (R : Type) [CommRing R] (C J : Cx R) : Prop :=
  ∀ (s t : ℤ) (V : Scheme.{0}) (x : Sec (C.X s) V ⊗[ULift.{1} R] Sec (J.X t) V),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x = 0 →
    Loc V fun W k => ∃ z : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] Sec (J.X t) W,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id z =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom x

def EtaleTensorWithFlatPreservesLocalExactness : Prop :=
  ∀ (R : Type) [CommRing R] {C J : Cx R}, (∀ t, FlatS (J.X t)) →
    (∀ (s : ℤ) (U : Scheme.{0}) (y : Sec (C.sc s).X₂ U), Sec.map (C.sc s).g y = 0 →
      Loc U fun V g => ∃ x : Sec (C.sc s).X₁ V, Sec.map (C.sc s).f x = Sec.res g y) →
    stair_row R C J

def EtaleTensorCycleLocallyLowersTopDegree : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → stair_row R C J →
    ∀ (w s : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, s < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ x' : Tens C J V w, (∀ p, s - 1 < p.1.1 → x' p = 0) ∧
        ∃ z : Sec (T.sc w).X₁ V, τ.lift V w x' = Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)

theorem etale_tensor_cycles_locally_lift_of_row_exact_and_descent (hA : EtaleTensorWithFlatPreservesLocalExactness)
    (hS : EtaleTensorCycleLocallyLowersTopDegree) : EtaleTensorCyclesLocallyLiftOfFlatBounded := by
  intro R _ C J T a b _ _ τ hτ hJ hC
  have hrow := hA R hJ hC
  have key : ∀ n : ℕ, ∀ (w : ℤ) (U : Scheme.{0}) (x : Tens C J U w), (∀ p, a - 1 + n < p.1.1 → x p = 0) →
      Sec.map (T.sc w).g (τ.lift U w x) = 0 →
      Loc U fun V g => ∃ z : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z = Sec.res g (τ.lift U w x) := by
    intro n
    induction n with
    | zero =>
      intro w U x hx _
      have h0 : x = 0 := by
        ext p
        by_cases hp : p.1.1 < a
        · simpa using stair_tens_low a x p hp
        · simpa using hx p (by push_cast; omega)
      refine stair_loc_top _ _ fun V g => ⟨0, ?_⟩
      simp [h0] <;> rfl
    | succ n ih =>
      intro w U x hx hc
      refine stair_loc_bind U _ _ (hS R τ hτ hrow w (a - 1 + (n + 1 : ℕ)) U x hx hc) ?_
      rintro V g ⟨x', hx', z, hz⟩
      have hc' : Sec.map (T.sc w).g (τ.lift V w x') = 0 := by
        rw [hz]
        have e1 : Sec.map (T.sc w).g (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
            Sec.map (T.sc w).g (Sec.res g (τ.lift U w x)) - Sec.map (T.sc w).g (Sec.map (T.sc w).f z) := by
          exact map_sub _ _ _
        rw [e1, stair_fg_zero, sub_zero]
        exact (stair_map_res (T.sc w).g g (τ.lift U w x)).trans ((congrArg (Sec.res g) hc).trans (map_zero _))
      refine stair_loc_mono V _ _ (ih w V x' (fun p hp => hx' p (by push_cast at hp ⊢; omega)) hc') ?_
      rintro W k ⟨z', hz'⟩
      refine ⟨z' + Sec.res k z, ?_⟩
      have e2 : Sec.map (T.sc w).f (z' + Sec.res k z) = Sec.map (T.sc w).f z' + Sec.map (T.sc w).f (Sec.res k z) := by
        simp only [Sec.map, map_add (f := _)]
      have e3 : Sec.res k (Sec.res g (τ.lift U w x) - (show Sec (T.X w) V from Sec.map (T.sc w).f z)) =
          Sec.res k (Sec.res g (τ.lift U w x)) - Sec.res k (show Sec (T.X w) V from Sec.map (T.sc w).f z) := by
        exact map_sub _ _ _
      rw [e2, hz', hz, e3, stair_map_res, stair_res_res]
      exact sub_add_cancel _ _
  intro w U x hx
  obtain ⟨s, hs⟩ := stair_tens_top x
  exact key (s - (a - 1)).toNat w U x (fun p hp => hs p (by omega)) hx

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorPairingSectionsLocallyFiniteSums
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTensorPairingSectionsLocallyFiniteSums : Prop :=
  ∀ (R : Type) [CommRing R] (F G T : Shv R) (μ : Pair (sgl F) (sgl G) (sgl T)), μ.IsTensor →
    ∀ (U : Scheme.{0}) (y : Sec ((sgl T).X 0) U), Loc U fun V g => ∃ (n : ℕ) (a : Fin n → Sec F V) (b : Fin n → Sec G V),
      Sec.res g y = ∑ m, μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι F) (a m)) (Sec.map (sglι G) (b m))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q i) U) (b : Sec (tw q j) U), Loc U fun V g => ∃ c : Sec (tw q k) V,
      Sec.map (sglι T) (Sec.map φ c) =
        μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (Sec.res g a)) (Sec.map (sglι _) (Sec.res g b))

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf

variable {R : Type} [CommRing R]

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem loc_top' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_bind' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, h'⟩ := h
  choose T hT hP using h'
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g hg, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hP V g hg W k hk

theorem loc_fin {U : Scheme.{0}} : ∀ (n : ℕ) (P : Fin n → ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ m, Loc U (P m)) → Loc U fun V g => ∀ m, P m V g
  | 0, _, _ => loc_top' fun _ _ m => m.elim0
  | n + 1, P, h => loc_mono' (loc_and' (h 0) (loc_fin n (fun m => P m.succ) fun m => h m.succ))
      fun _ _ hv m => Fin.cases hv.1 hv.2 m

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  simp [Sec.res]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem sglι_inj (F : Shv R) {U : Scheme.{0}} {x y : Sec F U}
    (h : Sec.map (sglι F) x = Sec.map (sglι F) y) : x = y := by
  have e : ∀ z : Sec F U, Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
      (Sec.map (sglι F) z) = z := by
    intro z
    change Sec.map (sglι F ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom) z = z
    rw [sglι]
    erw [Iso.inv_hom_id]
    exact map_id' z
  rw [← e x, ← e y, h]

end LateralTheory.EtaleFoundations.GenIsoSurjPf

namespace LateralTheory.EtaleFoundations.GenIsoSurjPf

variable {R : Type} [CommRing R]

theorem sec_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [hF.eq_of_src (𝟙 F) 0]
  rw [map_id'] at h1
  rw [h1]
  simp [Sec.map]

theorem sglι_surj (F : Shv R) {U : Scheme.{0}} (y : Sec ((sgl F).X 0) U) : ∃ a : Sec F U, Sec.map (sglι F) a = y := by
  refine ⟨Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom y, ?_⟩
  change Sec.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ sglι F) y = y
  rw [sglι]
  erw [Iso.hom_inv_id]
  exact map_id' y

def IsSum {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) (z : Sec ((sgl T).X 0) V) : Prop :=
  ∃ (n : ℕ) (a : Fin n → Sec F V) (b : Fin n → Sec G V),
    z = ∑ m, μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι F) (a m)) (Sec.map (sglι G) (b m))

theorem isSum_zero {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) : IsSum μ V 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

theorem isSum_add {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0}) {z w : Sec ((sgl T).X 0) V}
    (hz : IsSum μ V z) (hw : IsSum μ V w) : IsSum μ V (z + w) := by
  obtain ⟨n, a, b, rfl⟩ := hz
  obtain ⟨n', a', b', rfl⟩ := hw
  refine ⟨n + n', Fin.append a a', Fin.append b b', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSum_lift {F G T : Shv R} (μ : Pair (sgl F) (sgl G) (sgl T)) (V : Scheme.{0})
    (x : Tens (sgl F) (sgl G) V 0) : IsSum μ V (μ.lift V 0 x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using isSum_zero μ V
  | add x y hx hy => simpa using isSum_add μ V hx hy
  | of p t =>
    obtain ⟨⟨s, u⟩, hsu⟩ := p
    have hl : μ.lift V 0 (DirectSum.of _ ⟨⟨s, u⟩, hsu⟩ t) = TensorProduct.lift (μ.mul V s u 0 hsu) t := by
      simp [Pair.lift, ← DirectSum.lof_eq_of (ULift.{1} R)]
    rw [hl]
    clear hl
    induction t using TensorProduct.induction_on with
    | zero => simpa using isSum_zero μ V
    | add x y hx hy => simpa using isSum_add μ V hx hy
    | tmul a b =>
      simp only [TensorProduct.lift.tmul]
      by_cases hs : s = 0
      · subst hs
        have hu : u = 0 := by simpa using hsu
        subst hu
        obtain ⟨a', rfl⟩ := sglι_surj F a
        obtain ⟨b', rfl⟩ := sglι_surj G b
        exact ⟨1, fun _ => a', fun _ => b', by simp⟩
      · have ha : a = 0 := sec_zero_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F s hs) a
        rw [ha]
        simpa using isSum_zero μ V

theorem etale_tensor_pairing_sections_locally_finite_sums : LateralTheory.EtaleFoundations.EtaleTensorPairingSectionsLocallyFiniteSums := by
  intro R _ F G T μ hμ U y
  refine loc_mono' (hμ.1 U 0 y) fun V g ⟨x, hx⟩ => ?_
  obtain ⟨n, a, b, h⟩ := isSum_lift μ V x
  exact ⟨n, a, b, hx ▸ h⟩

end LateralTheory.EtaleFoundations.GenIsoSurjPf

open LateralTheory.EtaleFoundations.GenIsoSurjPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_locally_surjective_of_pairs (hp : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapHitsProductsLocally) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective := by
  intro q _ i j k T μ hμ hk φ hφ U b
  refine loc_bind' (loc_mono' (etale_tensor_pairing_sections_locally_finite_sums (ZMod q) _ _ _ μ hμ U (Sec.map (sglι T) b)) fun V g ⟨n, a, c, hy⟩ => ?_)
  refine loc_mono' (loc_fin n _ fun m => hp q i j k T μ hk φ hφ V (a m) (c m)) fun W h hW => ?_
  choose e he using hW
  refine ⟨∑ m, e m, sglι_inj T ?_⟩
  rw [← res_map, ← res_res, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, he, μ.nat, res_map]
end
end

-- bundled from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotientAndPreshe
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem kt_mono_sh (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G)
    (hι : ∀ A, Function.Injective (ι.app A).hom) :
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι)) := by
  have : ∀ U, Mono ((Functor.whiskerLeft Scheme.Γ ι).app U) := fun U =>
    (ModuleCat.mono_iff_injective _).2 (hι _)
  have : Mono (Functor.whiskerLeft Scheme.Γ ι) := NatTrans.mono_of_mono_app _
  infer_instance

theorem kt_res_sec (q : ℕ) (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : G.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec (R := ZMod q) G U x) = ofRings.sec (R := ZMod q) G V ((G.map g.appTop).hom x) := by
  unfold Sec.res ofRings.sec ofRings
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ G)).naturality g.op)
  exact this.symm

theorem kt_map_sec (q : ℕ) (T G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G) (U : Scheme.{0})
    (x : T.obj Γ(U, ⊤)) :
    Sec.map ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι))
      (ofRings.sec (R := ZMod q) T U x) = ofRings.sec (R := ZMod q) G U ((ι.app _).hom x) := by
  unfold Sec.map ofRings.sec
  have := congrArg (fun f => (ModuleCat.Hom.hom (NatTrans.app f (op U))) x)
    (toSheafify_naturality Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ ι))
  exact this.symm

def MuTwistQuotientEmbedsInUnitTorsorPresheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (G : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (ι : T ⟶ G),
      (∀ A, Function.Injective (ι.app A).hom) ∧
      ∃ s : ∀ A : CommRingCat.{0}, Aˣ → G.obj A,
        (∀ (A B : CommRingCat.{0}) (f : A ⟶ B) (v : Aˣ), (G.map f).hom (s A v) = s B (Units.map f.hom.toMonoidHom v)) ∧
        ∀ (A : CommRingCat.{0}) (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v →
          s A w = s A v + (ι.app A).hom ((τ.app A).hom (twGenR A ζ))

theorem etale_mu_twist_mono_extends_of_presheaf_torsor_embedding (hpre : MuTwistQuotientEmbedsInUnitTorsorPresheaf) : EtaleMuTwistMonoExtendsToTorsorSheaf := by
  intro q _ T τ hm hl
  obtain ⟨G, ι, hι, s, hs, hr⟩ := hpre q T τ hl
  have hmι := kt_mono_sh q T G ι hι
  refine ⟨ofRings (ZMod q) G, (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ) ≫
    (presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ ι), @mono_comp _ _ _ _ _ _ hm _ hmι,
    fun U v => ofRings.sec (R := ZMod q) G U (s _ v), ?_, ?_⟩
  · intro V U g v _
    rw [kt_res_sec]
    exact congrArg _ (hs _ _ g.appTop v)
  · intro U ζ v w h
    beta_reduce
    rw [hr _ ζ v w h]
    rw [show ofRings.sec (R := ZMod q) G U (s _ v + (ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) =
      ofRings.sec (R := ZMod q) G U (s _ v) + ofRings.sec (R := ZMod q) G U ((ι.app _).hom ((τ.app _).hom (twGenR _ ζ))) by
        unfold ofRings.sec
        exact map_add _ _ _]
    congr 1
    exact ((kt_map_sec q T G ι U _).symm.trans (congrArg _ (kt_map_sec q (twF q 1) T τ U (twGenR _ ζ)).symm))

theorem exists_etale_mono_mu_twist_into_torsor_sheaf_of_presheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : MuTwistQuotientEmbedsInUnitTorsorPresheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist :=
  exists_etale_mono_muTwist_into_torsorSheaf h1 (etale_mu_twist_mono_extends_of_presheaf_torsor_embedding h2)
end LateralTheory.EtaleFoundations
end

