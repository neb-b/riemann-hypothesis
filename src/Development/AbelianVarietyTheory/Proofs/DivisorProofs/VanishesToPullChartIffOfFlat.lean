module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)
open H0

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' T : Scheme.{0}} {φ : Y' ⟶ Y}

section Ideal

variable {L : LB Y} {L' : LB Y'} {ι : Type}

theorem secGer_chartSec (l : ChartPull L' L φ) (s : ι → L.Sec) (j : L'.ι) (z : Y') (hj : z ∈ L'.U j)
    (i : ι) : secGer (fun i => chartSec l (s i)) j z hj i =
      (φ.stalkMap z).hom (secGer s (l.idx j) (φ z) (l.le j hj) i) :=
  ger_appLE φ (l.le j) z hj _

theorem stalkId_cutIdeal_chartSec (hL : L.IsLB) (hL' : L'.IsLB) (l : ChartPull L' L φ)
    (s : ι → L.Sec) (z : Y') : stalkId (cutIdeal hL' fun i => chartSec l (s i)) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom := by
  obtain ⟨j, hj⟩ := exists_chart hL' z
  rw [stalkId_cutIdeal hL' _ j z hj, stalkId_cutIdeal hL s _ _ (l.le j hj), Ideal.map_span,
    ← Set.range_comp]
  exact congrArg (fun f => Ideal.span (Set.range f)) (funext (secGer_chartSec l s j z hj))

theorem stalkId_cutIdeal_secPull (hL : L.IsLB) (s : ι → L.Sec) (z : Y') :
    stalkId (cutIdeal (LB.isLB_pull hL φ) fun i => secPull (s i) φ) z =
      (stalkId (cutIdeal hL s) (φ z)).map (φ.stalkMap z).hom :=
  stalkId_cutIdeal_chartSec hL _ (GlobalTheory.chartPullPull L φ) s z

variable {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}

theorem le_ker_iff_stalk (t : T ⟶ Y) :
    I ≤ t.ker ↔ ∀ z, stalkId I (t z) ≤ RingHom.ker (t.stalkMap z).hom := by
  refine ⟨fun h z => ?_, fun h => Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_⟩
  · obtain ⟨W, hW, -⟩ := exists_affine (U := ⊤) (y := t z) trivial
    rw [ds_stalkId_eq_map I W _ hW, Ideal.map_le_iff_le_comap]
    intro a ha
    have h₀ : (t.app W.1).hom a = 0 := t.ideal_ker_le W (h W ha)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hW a).trans ((congrArg _ h₀).trans (map_zero _))
  · refine fun_ext_ger (U := t ⁻¹ᵁ U.1) fun z hz => ?_
    have := h z ((mem_ideal_iff_ger I U a).1 ha _ hz)
    exact (Scheme.Hom.germ_stalkMap_apply t _ z hz a).symm.trans (this.trans (map_zero _).symm)

variable (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)
include hI

theorem le_ker_iff_comp (t : T ⟶ Y') : I' ≤ t.ker ↔ I ≤ (t ≫ φ).ker := by
  rw [le_ker_iff_stalk, le_ker_iff_stalk]
  refine forall_congr' fun z => ?_
  rw [hI, Ideal.map_le_iff_le_comap, RingHom.comap_ker, Scheme.Hom.stalkMap_comp]
  rfl

theorem le_map_of_stalk : I ≤ I'.map φ := (le_ker_iff_comp hI _).1 I'.ker_subschemeι.ge

theorem eq_comap_of_stalk : I' = I.comap φ :=
  le_antisymm ((le_ker_iff_comp hI _).2 (by
      rw [Limits.pullback.condition]
      exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)))
    (Scheme.IdealSheafData.le_map_iff_comap_le.1 (le_map_of_stalk hI))

end Ideal

section Order

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {B : LB Y} {B' : LB Y'} {O : Y.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {n : ℕ}
  (hI : ∀ z, stalkId I' z = (stalkId I (φ z)).map (φ.stalkMap z).hom)




end Order

section On

variable {S S' : Scheme.{0}} {u : S ⟶ Y} {u' : S' ⟶ Y'} {ψ : S' ⟶ S}

theorem stalkMap_square (hψ : ψ ≫ u = u' ≫ φ) (z : S') {U : Y.Opens} (h : u (ψ z) ∈ U)
    (h' : φ (u' z) ∈ U) (x : Γ(Y, U)) :
    (ψ.stalkMap z).hom ((u.stalkMap (ψ z)).hom (ger _ h x)) =
      (u'.stalkMap z).hom ((φ.stalkMap (u' z)).hom (ger _ h' x)) := by
  have key {r r' : S' ⟶ Y} (e : r = r') (h : r z ∈ U) (h' : r' z ∈ U) :
      (r.stalkMap z).hom (ger _ h x) = (r'.stalkMap z).hom (ger _ h' x) := by
    subst e
    rfl
  have := key hψ h h'
  rwa [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at this

theorem pt_square (hψ : ψ ≫ u = u' ≫ φ) (z : S') : u (ψ z) = φ (u' z) :=
  congrArg (fun r : S' ⟶ Y => r z) hψ

theorem exists_stalkHom (hψ : ψ ≫ u = u' ≫ φ) (z : S') :
    ∃ θ : Y.presheaf.stalk (u (ψ z)) →+* Y'.presheaf.stalk (u' z),
      (∀ (U : Y.Opens) h h' (x : Γ(Y, U)),
        θ (ger _ h x) = (φ.stalkMap (u' z)).hom (ger _ h' x)) ∧
      ∀ x, (u'.stalkMap z).hom (θ x) = (ψ.stalkMap z).hom ((u.stalkMap (ψ z)).hom x) := by
  have key (y : Y) (e : y = φ (u' z)) : ∃ θ : Y.presheaf.stalk y →+* Y'.presheaf.stalk (u' z),
      ∀ (U : Y.Opens) h h' (x : Γ(Y, U)),
        θ (ger _ h x) = (φ.stalkMap (u' z)).hom (ger _ h' x) := by
    subst e
    exact ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨θ, hθ⟩ := key _ (pt_square hψ z)
  refine ⟨θ, hθ, fun x => ?_⟩
  obtain ⟨U, hU, x, rfl⟩ := Y.presheaf.germ_exist x
  exact (congrArg _ (hθ U hU (pt_square hψ z ▸ hU) x)).trans (stalkMap_square hψ z hU _ x).symm

variable {B : LB Y} {B' : LB Y'}

def chartPullOn (a : ChartPull B' B φ) (hψ : ψ ≫ u = u' ≫ φ) :
    ChartPull (B'.pull u') (B.pull u) ψ where
  idx J _ := a.idx (J PUnit.unit)
  le J z hz := mem_pull.2 ((pt_square hψ z).symm ▸ a.le _ (mem_pull.1 hz))
  g z J J' hJ hJ' := by
    have h := memInf (a.le _ (mem_pull.1 hJ)) (a.le _ (mem_pull.1 hJ'))
    have h' : u (ψ z) ∈ B.U (a.idx (J PUnit.unit)) ⊓ B.U (a.idx (J' PUnit.unit)) :=
      (pt_square hψ z).symm ▸ h
    refine ((tr_pull B' u' z hJ hJ').trans ?_).trans (gm_pull_g B u ψ z (fun _ => _) (fun _ => _)
      (mem_pull.2 h'.1) (mem_pull.2 h'.2)).symm
    rw [tr_chartPull a _ (mem_pull.1 hJ) (mem_pull.1 hJ'), hψ]
    refine Units.ext (Eq.trans ?_ (gm_val (u' ≫ φ) z _ h _).symm)
    refine (congrArg (fun x => (u'.stalkMap z).hom ((φ.stalkMap (u' z)).hom x))
      (val_tr B _ h)).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply (u' ≫ φ) _ z h _)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {O : Y.Opens} {W : Y'.Opens}
  {I : Y.IdealSheafData} {I' : Y'.IdealSheafData} {ψ : I'.subscheme ⟶ I.subscheme}

def pullOn (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) : sectionsOnClosedSubscheme p B I →ₛₗ[σ] sectionsOnClosedSubscheme p' B' I' :=
  pullChart (chartPullOn a hψ) (by rw [← Category.assoc, hψ, Category.assoc, w, Category.assoc])
    le_top

theorem germ_pullOn (a : ChartPull B' B φ) (w : φ ≫ p = p' ≫ spMap σ)
    (hψ : ψ ≫ I.subschemeι = I'.subschemeι ≫ φ) (g : sectionsOnClosedSubscheme p B I) (j : (B'.pull I'.subschemeι).ι)
    (z : I'.subscheme) (hj : z ∈ (B'.pull I'.subschemeι).U j) :
    germ j z (Opens.mem_top z) hj (pullOn a w hψ g) = (ψ.stalkMap z).hom
      (germ (fun _ => a.idx (j PUnit.unit)) (ψ z) (Opens.mem_top _)
        ((chartPullOn a hψ).le j hj) g) :=
  germ_pullChart _ _ _ g j z _ hj

end On

theorem LeadAt.map {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    {ι : Type} [Finite ι] {π : R →+* S} {π' : R' →+* S'} {x : ι → R} {a : ℕ} {f : R}
    {γ : MonoDeg ι a → S} (h : LeadAt π x f γ) (θ : R →+* R') (η : S →+* S')
    (e : ∀ r, π' (θ r) = η (π r)) : LeadAt π' (fun i => θ (x i)) (θ f) fun α => η (γ α) := by
  obtain ⟨m, hm, hf⟩ := h
  refine ⟨fun α => θ (m α), fun α => by rw [e, hm], ?_⟩
  have := Ideal.mem_map_of_mem θ hf
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, map_monoVal] at this
  exact this

section Lead

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} {L M : LB Y} {L' M' : LB Y'}
  {hL : L.IsLB} {hL' : L'.IsLB} {ι : Type} [Finite ι] {s : ι → L.Sec} {O : Y.Opens} {W : Y'.Opens}

theorem HasLead.pullChart (m : ChartPull M' M φ) (l : ChartPull L' L φ) (w : φ ≫ p = p' ≫ spMap σ)
    {ψ : (cutIdeal hL' fun i => chartSec l (s i)).subscheme ⟶ (cutIdeal hL s).subscheme}
    (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun i => chartSec l (s i)).subschemeι ≫ φ)
    (hW : W ≤ φ ⁻¹ᵁ O) {hO : SuppIn O (cutIdeal hL s)}
    (hO' : SuppIn W (cutIdeal hL' fun i => chartSec l (s i))) {n d : ℤ} {a : ℕ} {h : n + a = d}
    {f : H0 p (tw M L d) O} {c : MonoDeg ι a → sectionsOnClosedSubscheme p (tw M L n) (cutIdeal hL s)}
    (e : HasLead hL s hO h f c) :
    HasLead hL' _ hO' h (pullChart (chartPullTwist m l d) w hW f)
      fun α => pullOn (chartPullTwist m l n) w hψ (c α) := fun z i j hi hj => by
  obtain ⟨θ, hθ, hθ'⟩ := exists_stalkHom hψ z
  have := (e (ψ z) (m.idx i) (l.idx j) ((pt_square hψ z).symm ▸ m.le i hi)
    ((pt_square hψ z).symm ▸ l.le j hj)).map θ (ψ.stalkMap z).hom hθ'
  convert this using 1
  · exact funext fun t => (secGer_chartSec l s j _ hj t).trans (hθ _ _ _ _).symm
  · exact (germ_pullChart _ _ _ _ _ _ _ _).trans (hθ _ _ _ _).symm
  · exact funext fun α => germ_pullOn _ _ _ _ _ _ _

end Lead

section Symbol

variable {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {σ : k →+* k'} (H : IsPullback φ p' p (spMap σ))




variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {L A B : LB Y} {L' A' B' : LB Y'} (l : ChartPull L' L φ) (a : ChartPull A' A φ)
  (b : ChartPull B' B φ) (s : Fin D → L.Sec)

abbrev pullQuotSec (e : (LB.div A (tw B L D)).Sec) : (LB.div A' (tw B' L' D)).Sec :=
  chartSec (chartPullQuot a (chartPullTwist b l D)) e

variable (hL : L.IsLB) (hA : A.IsLB) (hB : B.IsLB) (hL' : L'.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (e : (LB.div A (tw B L D)).Sec)


variable (hS : Etale ((cutIdeal hL s).subschemeι ≫ p))
  (hS' : Etale ((cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ p'))
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s))
  (he' : SuppIn (nonzeroLocus (pullQuotSec l a b e)) (cutIdeal hL' fun t => chartSec l (s t)))
  {ψ : (cutIdeal hL' fun t => chartSec l (s t)).subscheme ⟶ (cutIdeal hL s).subscheme}
  (hψ : ψ ≫ (cutIdeal hL s).subschemeι = (cutIdeal hL' fun t => chartSec l (s t)).subschemeι ≫ φ)

variable {O : Y.Opens} {W : Y'.Opens} (hW : W ≤ φ ⁻¹ᵁ O) (hO : SuppIn O (cutIdeal hL s))
  (hO' : SuppIn W (cutIdeal hL' fun t => chartSec l (s t)))

end Symbol

section Field

variable {E E' : Type} [Field E] [Field E'] {σ : E →+* E'} {p : Y ⟶ Sp E} {p' : Y' ⟶ Sp E'}
  (H : IsPullback φ p' p (spMap σ)) {L : LB Y} (hL : L.IsLB)




section Order

variable {ι : Type} (s : ι → L.Sec) {B : LB Y} {B' : LB Y'} {O : Y.Opens} {n : ℕ}

end Order

variable {D : ℕ} [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] (K : CanonLB p D)
  {A B : LB Y} {A' B' : LB Y'} (hA : A.IsLB) (hB : B.IsLB) (hA' : A'.IsLB) (hB' : B'.IsLB)
  (a : ChartPull A' A φ) (b : ChartPull B' B φ) (s : Fin D → L.Sec)
  (hS : Etale ((cutIdeal hL s).subschemeι ≫ p)) (e : (LB.div A (tw B L D)).Sec)
  (he : SuppIn (nonzeroLocus e) (cutIdeal hL s)) {O : Y.Opens} (hO : SuppIn O (cutIdeal hL s))

end Field

end GlobalTheory.Vanishing
