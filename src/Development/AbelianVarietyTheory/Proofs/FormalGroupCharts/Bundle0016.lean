module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
section
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.JetSer

section Val
variable {A : Type} [CommRing A] {X : Scheme.{0}}

def fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem fnVal_eq_fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal p U f = fnValHom p U h f := by
  unfold fnVal
  rw [dite_eq_left h]
  rfl

theorem top_le_preimage_comp {T T' : Scheme.{0}} (r : T' ⟶ T) (p : T ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (r ≫ p) ⁻¹ᵁ U := fun z _ => by
  have : r z ∈ p ⁻¹ᵁ U := h trivial
  simpa using this

theorem fnVal_specMap {B : Type} [CommRing B] (ψ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal (Spec.map (CommRingCat.ofHom ψ) ≫ p) U f = ψ (fnVal p U f) := by
  have h' := top_le_preimage_comp (Spec.map (CommRingCat.ofHom ψ)) p U h
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  have e : (Spec.map (CommRingCat.ofHom ψ) ≫ p).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ CommRingCat.ofHom ψ := by
    rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) p U ⊤ ⊤ h le_top]
    congr 2
  unfold fnValHom
  rw [e]
  rfl

theorem fnVal_comp {Y : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ q ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(Y, V)) :
    ⊤ ≤ (p ≫ q) ⁻¹ᵁ V ∧ fnVal (p ≫ q) V f = fnVal p U ((q.appLE V U hUV).hom f) := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := fun z _ => by
    have : p z ∈ q ⁻¹ᵁ V := hUV (h trivial)
    simpa using this
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.appLE_comp_appLE p q V U ⊤ hUV h]
  rfl

theorem fnVal_res (p : Spec (CommRingCat.of A) ⟶ X) (U V : X.Opens) (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)) :
    ⊤ ≤ p ⁻¹ᵁ V ∧ fnVal p V f = fnVal p U ((X.presheaf.map (homOfLE hUV).op).hom f) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ V := fun z _ => hUV (h trivial)
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.map_appLE p h (homOfLE hUV).op]
  rfl

theorem top_le_preimage_of_nil {B : Type} [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro z _
  have hker : RingHom.ker q ≤ z.asIdeal := fun a ha => by
    obtain ⟨n, hn⟩ := hn a ha
    exact z.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have := z.isPrime
  have hprime : (z.asIdeal.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let z₀ : ↥(Spec (CommRingCat.of B)) := (⟨z.asIdeal.map q, hprime⟩ : PrimeSpectrum B)
  have hz : (Spec.map (CommRingCat.ofHom q)) z₀ = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q z.asIdeal) = z.asIdeal
    rw [Ideal.comap_map_of_surjective' q hq, sup_eq_left.mpr hker]
  have h0 : z₀ ∈ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U := h trivial
  rw [← hz]
  simpa using h0

end Val

section Jet
variable {R : Type} [CommRing R] {κ : Type}

theorem jetTruncR_surjective (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem isNilpotent_of_mem_ker_jetTruncR (m : ℕ) (a : JetR R κ (m + 1))
    (ha : a ∈ RingHom.ker (jetTruncR R κ m).toRingHom) : IsNilpotent a := by
  have e : (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have ha' : jetTruncR R κ m a = 0 := ha
  have h1 : a ∈ RingHom.ker (jetAug R κ (m + 1)) := by
    rw [RingHom.mem_ker, ← e, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  have := Ideal.pow_mem_pow h1 (m + 1 + 1)
  rwa [ker_jetAug_pow, Ideal.mem_bot] at this

theorem top_le_preimage_jet {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (hp : ∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) (U : X.Opens) (h : ⊤ ≤ p 0 ⁻¹ᵁ U) (m : ℕ) :
    ⊤ ≤ p m ⁻¹ᵁ U := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [← hp m] at ih
    exact top_le_preimage_of_nil (jetTruncR R κ m).toRingHom (jetTruncR_surjective m)
      (isNilpotent_of_mem_ker_jetTruncR m) _ U ih

end Jet

theorem serSt_of_jetAlgSt : JetAlgSt → SerSt := by
  intro hJ R _ κ _ X p hp U h0
  have hU := top_le_preimage_jet p hp U h0
  obtain ⟨hτ, -, hinj, hex, -⟩ := hJ R κ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : ∀ f : Γ(X, U), ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = fnValHom (p m) U (hU m) f := by
      intro f
      refine hex (fun m => fnValHom (p m) U (hU m) f) fun m => ?_
      have := fnVal_specMap (jetTruncR R κ m).toRingHom (p (m + 1)) U (hU _) f
      rw [← spMap_left, hp m, fnVal_eq_fnValHom _ _ (hU _), fnVal_eq_fnValHom _ _ (hU _)] at this
      exact this.symm
    choose T hT using hc
    choose τ hτ₁ hτ₂ using hτ
    refine ⟨{ toFun := T
              map_one' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_one, map_one]
              map_mul' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_mul, map_mul, hτ₁, hτ₁, hT, hT]
              map_zero' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_zero, map_zero]
              map_add' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_add (f := _), map_add (f := _), hτ₁, hτ₁, hT, hT] }, fun f g => ⟨fun H => ?_, fun H m => ?_⟩⟩
    · exact hinj _ _ fun m => by
        rw [← (H m).2, fnVal_eq_fnValHom _ _ (hU m)]
        exact (hT f m).symm
    · refine ⟨hU m, ?_⟩
      rw [H, fnVal_eq_fnValHom _ _ (hU m)]
      exact (hT f m).symm
  · intro V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_res (p m) U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro Y q V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_comp (p m) q U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro κ' _ b ψ hb hψ f g H m
    refine ⟨top_le_preimage_comp _ _ U (hU m), ?_⟩
    have := fnVal_specMap (ψ m).toRingHom (p m) U (hU m) f
    rw [(H m).2] at this
    exact this.trans (((hJ R κ').2.2.2.2 κ b hb m).2 (ψ m) (hψ m) g)

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChart
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartUniv

section Jets
open ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem jetAug_eq (κ : Type) (m : ℕ) : jetAug R κ m = (jetAug R κ 0).comp (jetZeroR R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm

theorem jetZero_zR (κ : Type) (m : ℕ) (j : κ) : jetZeroR R κ m (zR m j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact Ideal.subset_span ⟨j, rfl⟩)

theorem jetZero_eq (κ : Type) (m : ℕ) : jetZeroR R κ m = (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR, map_zero, jetZero_zR]

theorem aug_comp_iff {κ κ' : Type} {m : ℕ} (ψ : JetR R κ m →ₐ[R] JetR R κ' m) :
    (jetAug R κ' m).comp ψ = jetAug R κ m ↔ ∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    have := AlgHom.congr_fun h (zR m j)
    rw [AlgHom.comp_apply, jetAug_zR] at this
    rw [jetZero_eq, AlgHom.comp_apply, this, map_zero]
  · intro h
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, jetAug_zR, jetAug_eq, AlgHom.comp_apply, h, map_zero]

theorem spMap_id' (A : Type) [CommRing A] [Algebra R A] : spMap (R₀ := R) (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [spMap_left]
  exact Spec.map_id _

def jetRen {κ κ' : Type} (f : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  jetLift R (RingHom.ker (jetAug R κ' m)) (ker_jetAug_pow κ' m) (fun j => zR m (f j)) (fun j => zR_mem_ker m (f j))

theorem jetRen_zR {κ κ' : Type} (f : κ → κ') (m : ℕ) (j : κ) : jetRen (R := R) f m (zR m j) = zR m (f j) :=
  jetLift_zR _ _ _ _ j

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem univ_all [IsLocalRing R] [Smooth G.hom] {κ : Type} {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
    (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hA : (RingHom.ker aug) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap aug ≫ y = 1) :
    ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x := by
  obtain ⟨n, z, -, hz0, hzu⟩ := univChartLoc G
  have hxa : spMap (jetAug R κ m) ≫ x = 1 := by
    rw [jetAug_eq, ← spMap_comp, Category.assoc, h0, comp_one']
  obtain ⟨α, ⟨ha1, ha2⟩, -⟩ := hzu (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) x hxa
  obtain ⟨β, ⟨hb1, hb2⟩, -⟩ := hu (Fin n) (z m) (hz0 m)
  have hb1' := (aug_comp_iff β).2 hb1
  have hab : α.comp β = AlgHom.id R _ := by
    refine (hu κ x h0).unique ⟨(aug_comp_iff _).1 ?_, ?_⟩ ⟨fun j => jetZero_zR κ m j, ?_⟩
    · rw [← AlgHom.comp_assoc, ha1, hb1']
    · rw [← spMap_comp, Category.assoc, ← hb2, ← ha2]
    · rw [spMap_id', Category.id_comp]
  obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := hzu A aug m hA y hy
  refine ⟨ψ.comp β, ⟨?_, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, h1, hb1']
  · rw [← spMap_comp, Category.assoc, ← hb2, ← h2]
  · rintro φ ⟨g1, g2⟩
    have : φ.comp α = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, ha1], by
      rw [← spMap_comp, Category.assoc, ← ha2, ← g2]⟩
    rw [← this, AlgHom.comp_assoc, hab, AlgHom.comp_id]

theorem isUnivChart_ren [IsLocalRing R] [Smooth G.hom] {κ : Type} {d : ℕ} (e : κ ≃ Fin d)
    (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m)
    (h0 : ∀ m, spMap (jetZeroR R κ m) ≫ x m = 1)
    (hu : ∀ (κ' : Type) (m : ℕ) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m) :
    IsUnivChart G d (fun m => spMap (jetRen e m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hA y hy => ?_⟩
  · have : (jetTruncR R (Fin d) m).comp (jetRen e (m + 1)) = (jetRen e m).comp (jetTruncR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR]
        exact (jetRen_zR (R := R) e m j).symm
    show _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ht]
  · have : (jetZeroR R (Fin d) m).comp (jetRen e m) = (jetRen e 0).comp (jetZeroR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR, jetZero_zR, jetZero_zR, map_zero]
    show _ ≫ _ ≫ _ = _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, h0, comp_one']
  · obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := univ_all (x m) (h0 m) (fun κ' => hu κ' m) A aug hA y hy
    have e1 : (jetRen (R := R) e m).comp (jetRen e.symm m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.apply_symm_apply]; rfl
    have e2 : (jetRen (R := R) e.symm m).comp (jetRen e m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.symm_apply_apply]; rfl
    have a1 : (jetAug R κ m).comp (jetRen e.symm m) = jetAug R (Fin d) m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    have a2 : (jetAug R (Fin d) m).comp (jetRen e m) = jetAug R κ m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    refine ⟨ψ.comp (jetRen e.symm m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, h1, a1]
    · show y = _ ≫ _ ≫ _
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e2, AlgHom.comp_id]
      exact h2
    · rintro φ ⟨g1, g2⟩
      have : φ.comp (jetRen e m) = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, a2], by
        rw [← spMap_comp, Category.assoc]; exact g2⟩
      rw [← this, AlgHom.comp_assoc, e1, AlgHom.comp_id]

end Jets

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj

theorem isUnivChart_of_isChartJ : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by
  intro T _ _ G _ _ hG d F x hx
  haveI := hG
  let e : Fin 1 × Fin d ≃ Fin d := Equiv.uniqueProd (Fin d) (Fin 1)
  refine ⟨fun m => Chart.spMap (jetRen e m) ≫ x m,
    isUnivChart_ren e x hx.trunc hx.zero hx.univ, fun m => jetRen e m, fun m j => jetRen_zR e m _, fun m => rfl⟩

end GlobalTheory.ChartUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R]

theorem rep_jetAug_comp_trunc (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm

theorem rep_jetAug_comp_zero (κ : Type) (m : ℕ) :
    (jetAug R κ 0).comp (jetZeroR R κ m) = jetAug R κ m :=
  jet_ext fun j => (jetAug_zR 0 j).trans (jetAug_zR m j).symm

theorem isFPt_of_isUnivChart {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)}
    (hx : IsUnivChart G d x) : IsFPt x := by
  refine ⟨hx.1, fun m => ?_⟩
  rw [← rep_jetAug_comp_zero, ← spMap_comp, Category.assoc, hx.2.1 m]
  exact MonObj.comp_one _

theorem repSt_of_jetAlgSt (hJ : JetAlgSt) : RepSt := by
  intro R _ G _ d x hx κ _
  obtain ⟨hτ, htr, hinj, hsur, hsub⟩ := hJ R κ
  have hxa := (isFPt_of_isUnivChart hx).2
  have haug : ∀ (a : Fin d → MvPowerSeries κ R), (∀ j, constantCoeff (a j) = 0) → ∀ m
      (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m), (∀ j, ψ (zR m j) = toJet m (a j)) →
      (jetAug R κ m).comp ψ = jetAug R (Fin d) m := by
    intro a ha m ψ hψ
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, hψ, (htr m _).2, ha, jetAug_zR]
  have hfp : ∀ a (y : Fam G κ), Rep x a y → IsFPt y := by
    rintro a y ⟨ha, hy⟩
    choose ψ hψ hy using hy
    refine ⟨fun m => ?_, fun m => ?_⟩
    · have e : (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
        refine jet_ext fun j => ?_
        rw [AlgHom.comp_apply, hψ, (htr m _).1]
        exact (hψ m j).symm
      rw [hy, hy, ← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hx.1]
    · rw [hy, ← Category.assoc, spMap_comp, haug a ha m _ (hψ m), hxa]
  refine ⟨fun a ha => ?_, fun y hy => ?_, hfp, ⟨fun j => by simp, fun m => ?_⟩, ?_⟩
  · choose ψ hψ using fun m => (hsub (Fin d) a ha m).1
    refine ⟨fun m => spMap (ψ m) ≫ x m, ⟨ha, fun m => ⟨ψ m, hψ m, rfl⟩⟩, ?_⟩
    rintro y ⟨-, hy⟩
    funext m
    obtain ⟨ψ', h1, h2⟩ := hy m
    have : ψ' = ψ m := jet_ext fun j => (h1 j).trans (hψ m j).symm
    rw [h2, this]
  · have hU := fun m => hx.2.2 (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) (y m) (hy.2 m)
    choose ψ hψ hu using hU
    have hc : ∀ m, (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
      intro m
      have hk : RingHom.ker (jetAug R κ m) ^ (m + 1 + 1) = ⊥ := by
        rw [pow_succ (RingHom.ker (jetAug R κ m)) (m + 1), ker_jetAug_pow, Ideal.bot_mul]
      refine (hx.2.2 (JetR R κ m) (jetAug R κ m) (m + 1) hk (y m) (hy.2 m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [← AlgHom.comp_assoc, rep_jetAug_comp_trunc, (hψ (m + 1)).1]
      · rw [← spMap_comp, Category.assoc, ← (hψ (m + 1)).2, hy.1 m]
      · rw [← AlgHom.comp_assoc, (hψ m).1, rep_jetAug_comp_trunc]
      · rw [← spMap_comp, Category.assoc, hx.1 m, ← (hψ m).2]
    have hex : ∀ j, ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = ψ m (zR m j) := fun j =>
      hsur (fun m => ψ m (zR m j)) (fun m => AlgHom.congr_fun (hc m) (zR (m + 1) j))
    choose a ha using hex
    refine ⟨a, ⟨fun j => ?_, fun m => ⟨ψ m, fun j => (ha j m).symm, (hψ m).2⟩⟩, ?_⟩
    · rw [← (htr 0 _).2, ha, ← jetAug_zR (R := R) 0 j]
      exact AlgHom.congr_fun (hψ 0).1 _
    · rintro a' ⟨ha', hy'⟩
      funext j
      refine hinj _ _ fun m => ?_
      obtain ⟨ψ', h1, h2⟩ := hy' m
      rw [ha, ← h1, hu m ψ' ⟨haug a' ha' m ψ' h1, h2⟩]
  · refine ⟨(Algebra.ofId R _).comp (jetAug R (Fin d) m), fun j => ?_, ?_⟩
    · obtain ⟨τ, h, -⟩ := hτ m
      rw [AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, ← h, map_zero]
    · rw [← spMap_comp, Category.assoc, hxa]
      exact (MonObj.comp_one _).symm
  · rintro κ' _ b ψ hb hψ a y ⟨ha, hy⟩
    obtain ⟨-, htr', -, -, hsub'⟩ := hJ R κ'
    have hs := fun m => (hsub' κ b hb m).2 (ψ m) (hψ m)
    refine ⟨fun j => ?_, fun m => ?_⟩
    · have e : (jetAug R κ' 0).comp (ψ 0) = jetAug R κ 0 := by
        refine jet_ext fun i => ?_
        rw [AlgHom.comp_apply, hψ, (htr' 0 _).2, hb, jetAug_zR]
      rw [← (htr' 0 _).2, ← hs, ← ha j, ← (htr 0 _).2]
      exact AlgHom.congr_fun e _
    · obtain ⟨φ, h1, h2⟩ := hy m
      refine ⟨(ψ m).comp φ, fun j => ?_, ?_⟩
      · rw [AlgHom.comp_apply, h1, hs]
      · show spMap (ψ m) ≫ y m = _
        rw [h2, ← Category.assoc, spMap_comp]

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermExist

theorem isUnit_of_isSer1 (hrep : RepSt) (hser : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {U : G.left.Opens} {f : Γ(G.left, U)} (hf : IsUnit f) {r : PS R 1 d} (h : IsSer1 x U f r) : IsUnit r := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (gp_pt 0)
  have hc := (h3 _ y hy).1
  have hs := h 1 _ y hy
  have e : ev (n := 1) ![pt R (n := 1) d 0] r = r := by
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  rw [e] at hs
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hs 0).1
  rw [(hτ f r).1 hs]
  exact hf.map τ

theorem top_le_preimage_wchart {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : L.ι) (e : Z ⟶ Y) (h : ∀ k, ⊤ ≤ (e ≫ φ k) ⁻¹ᵁ L.U j) : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ (fun _ => j) := by
  intro z hz
  exact Set.mem_iInter.2 fun k => h k hz

theorem unit_comp_primφ {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) (hw : η[A] ≫ w = η[A])
    (k : Fin 5) : η[A].left ≫ primφ w k = η[A].left := by
  have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
    rw [MonObj.comp_one, Hom.one_def]
    simp
  have h2 : η[A] ≫ (𝟙 A * w : A ⟶ A) = η[A] := by
    rw [MonObj.comp_mul, hw, Category.comp_id]
    have : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by
      rw [Hom.one_def]; simp
    rw [this, _root_.mul_one]
  fin_cases k
  · exact Category.comp_id _
  · exact congrArg (·.left) h2
  · exact Category.comp_id _
  · exact congrArg (·.left) hw
  · exact congrArg (·.left) h1

theorem germ_exists_unique : JetAlgSt → RepSt → SerSt → SerExSt → GermExSt := by
  intro _ hrep hser hex R _ G _ L _ w hw ρ d x hx j hj m s
  obtain ⟨h1, -⟩ := hex R G d x hx
  obtain ⟨σ, hσ, uσ⟩ := h1 (LB.wchart L (K := PUnit) (fun _ => 𝟙 G.left) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.comp_id]; exact hj)) (s.f (fun _ => j))
  obtain ⟨r, hr, ur⟩ := h1 (LB.wchart L (primφ w) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun k => by rw [unit_comp_primφ w hw k]; exact hj)) (ρ.s (fun _ => j)).val
  have hu : IsUnit (r ^ m) := (isUnit_of_isSer1 hrep hser hx (Units.isUnit _) hr).pow m
  obtain ⟨v, hv⟩ := hu
  refine ⟨σ * (v⁻¹).val, ⟨σ, r, hσ, hr, by rw [← hv, Units.inv_mul_cancel_right]⟩, ?_⟩
  rintro f ⟨σ', r', hσ', hr', hf⟩
  rw [uσ σ' hσ', ur r' hr', ← hv] at hf
  rw [← hf, Units.mul_inv_cancel_right]

end GlobalTheory.GermExist
end
end

