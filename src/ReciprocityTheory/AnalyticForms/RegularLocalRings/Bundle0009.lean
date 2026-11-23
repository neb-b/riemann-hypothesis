module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0008
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.SegreIdealIsHomogeneous

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.BijOnClosedPointsOfIsIso
section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

theorem isClosed_of_isClosed_open [LocallyOfFiniteType sW] (V : W.Opens) (x : V)
    (hx : IsClosed ({x} : Set V)) : IsClosed ({x.1} : Set W) := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  apply isClosed_singleton_of_isLocallyClosed_singleton
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hx
  refine ⟨(V : Set W), t, V.isOpen, ht, ?_⟩
  ext z
  constructor
  · rintro rfl
    exact ⟨x.2, (Set.ext_iff.mp hteq x).mpr rfl⟩
  · rintro ⟨hzV, hzt⟩
    have e : (⟨z, hzV⟩ : V) = x := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
    show z = x.1
    exact congrArg Subtype.val e

theorem bijOn_closedPoints_of_isIso (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] :
    Set.BijOn π.base {x | IsClosed ({x} : Set W) ∧ π.base x ∈ U}
      {y | IsClosed ({y} : Set X) ∧ y ∈ U} := by
  let h := Scheme.homeoOfIso (asIso (π ∣_ U))
  have hb : ∀ z, (h z).1 = π.base z.1 := fun z => morphismRestrict_base_coe π U z
  refine ⟨fun x hx => ⟨isClosed_image_of_closed sW sX π hπ x hx.1, hx.2⟩, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ he
    have e1 : h ⟨x₁, hx₁.2⟩ = h ⟨x₂, hx₂.2⟩ :=
      Subtype.ext ((hb ⟨x₁, hx₁.2⟩).trans (he.trans (hb ⟨x₂, hx₂.2⟩).symm))
    exact congrArg Subtype.val (h.injective e1)
  · intro y hy
    let w := h.symm ⟨y, hy.2⟩
    have hw : h w = ⟨y, hy.2⟩ := h.apply_symm_apply _
    have hcl : IsClosed ({h w} : Set _) := by
      refine isClosed_induced_iff.mpr ⟨{y}, hy.1, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · exact Subtype.ext (hz.trans (congrArg Subtype.val hw).symm)
      · exact (congrArg Subtype.val hz).trans (congrArg Subtype.val hw)
    have hcw : IsClosed ({w} : Set _) := by
      have := hcl.preimage h.continuous
      rwa [← Set.image_singleton, h.injective.preimage_image] at this
    have hW : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
    refine ⟨w.1, ⟨?_, w.2⟩, (hb w).symm.trans (congrArg Subtype.val hw)⟩
    apply isClosed_singleton_of_isLocallyClosed_singleton
    obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hcw
    refine ⟨((π ⁻¹ᵁ U : W.Opens) : Set W), t, (π ⁻¹ᵁ U).isOpen, ht, ?_⟩
    ext z
    constructor
    · rintro rfl
      exact ⟨w.2, (Set.ext_iff.mp hteq w).mpr rfl⟩
    · rintro ⟨hzV, hzt⟩
      have e : (⟨z, hzV⟩ : ((π ⁻¹ᵁ U : W.Opens) : Set W)) = w := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
      show z = w.1
      exact congrArg Subtype.val e

theorem exists_coord_inv (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] (PW : AffPres sW) (V : X.Opens)
    (hV : IsAffineOpen V) {σ : Type} [Finite σ] (u : σ → Γ(X, V))
    (hu : ∀ t : Γ(X, V), ∃ F : MvPolynomial σ ℂ, t = eval₂ (constSec sX V) u F)
    (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V) (hxU : π.base x ∈ U)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ (U ⊓ V) ∧
      ∃ (q : MvPolynomial σ ℂ) (F : Fin PW.n → MvPolynomial σ ℂ),
        eval (fun t => val sX (u t) (π.base x) hxV) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (fun t => val sX (u t) (π.base y) hyV) q ≠ 0 ∧
          ∀ l, PW.coord y hyW l * eval (fun t => val sX (u t) (π.base y) hyV) q =
            eval (fun t => val sX (u t) (π.base y) hyV) (F l) := by
  have hiso : IsIso (π.stalkMap x) := by
    let x' : (π ⁻¹ᵁ U : W.Opens) := ⟨x, hxU⟩
    have h1 : IsIso ((π ∣_ U).stalkMap x') := by
      first
      | exact inferInstance
      | exact (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion (π ∣_ U))).2 x'
    have h2 : (MorphismProperty.isomorphisms CommRingCat) ((π ∣_ U).stalkMap x') := h1
    exact (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap π U x') |>.mp h2
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sX π hπ V hV u hu PW.V
    (fun l => PW.secHom (MvPolynomial.X l)) x hxW hxV hc (ConcreteCategory.bijective_of_isIso (π.stalkMap x)).2
  refine ⟨O ⊓ π ⁻¹ᵁ U, ⟨hxO, hxU⟩, ?_, q, F, hq, ?_⟩
  · intro y hy
    exact ⟨(hO hy.1).1, hy.2, (hO hy.1).2⟩
  · intro y hyW hyV hyO hcy
    obtain ⟨h1, h2⟩ := hF y hyW hyV hyO.1 hcy
    refine ⟨h1, fun l => ?_⟩
    rw [← h2 l, PW.val_secHom y hyW hcy, eval_X]

theorem exists_coord_fwd (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (PW : AffPres sW) (V : X.Opens) {σ : Type} [Finite σ]
    (u : σ → Γ(X, V)) (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial (Fin PW.n) ℂ) (F : σ → MvPolynomial (Fin PW.n) ℂ),
        eval (PW.coord x hxW) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (PW.coord y hyW) q ≠ 0 ∧
          ∀ t, val sX (u t) (π.base y) hyV * eval (PW.coord y hyW) q =
            eval (PW.coord y hyW) (F t) := by
  have : IsAffine PW.V.toScheme := IsAffine.of_isIso PW.iso.hom
  have hV : IsAffineOpen PW.V := this
  let u' : Fin PW.n → Γ(W, PW.V) := fun j => PW.secHom (MvPolynomial.X j)
  have hu' : ∀ a : Γ(W, PW.V), ∃ F : MvPolynomial (Fin PW.n) ℂ,
      a = eval₂ (constSec sW PW.V) u' F := by
    intro a
    obtain ⟨f, rfl⟩ := PW.secHom_surjective a
    refine ⟨f, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta f]
    rw [eval₂_comp_left]
    congr 1
    ext c
    exact PW.secHom_C c
  have hxW' : (𝟙 W : W ⟶ W).base x ∈ PW.V := hxW
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sW (𝟙 W) (Category.id_comp _) PW.V hV
    u' hu' (PW.V ⊓ π ⁻¹ᵁ V) (fun t => π.appLE V (PW.V ⊓ π ⁻¹ᵁ V) inf_le_right (u t)) x
    ⟨hxW, hxV⟩ hxW' hc (by rw [Scheme.Hom.stalkMap_id]; exact fun z => ⟨z, rfl⟩)
  have hcoord : ∀ (y : W) (hyW : y ∈ PW.V) (h : (𝟙 W : W ⟶ W).base y ∈ PW.V),
      IsClosed ({y} : Set W) → (fun a => val sW (u' a) ((𝟙 W : W ⟶ W).base y) h) = PW.coord y hyW := by
    intro y hyW h hcy
    funext j
    change val sW (PW.secHom (MvPolynomial.X j)) y hyW = _
    rw [PW.val_secHom y hyW hcy, eval_X]
  refine ⟨O, hxO, fun y hy => (hO hy).1, q, F, ?_, ?_⟩
  · rw [← hcoord x hxW hxW' hc]
    exact hq
  · intro y hyW hyV hyO hcy
    have hyW' : (𝟙 W : W ⟶ W).base y ∈ PW.V := hyW
    obtain ⟨h1, h2⟩ := hF y ⟨hyW, hyV⟩ hyW' hyO hcy
    rw [hcoord y hyW hyW' hcy] at h1 h2
    refine ⟨h1, fun t => ?_⟩
    rw [← h2 t, (val_comp sW sX π hπ inf_le_right (u t) y ⟨hyW, hyV⟩ hcy).2]

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AlgRes.IsGoodAtlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e)
    (A : FinHolAtlas e R.M) : Prop :=
      (∀ i (h : MvPolynomial (Fin (R.amb i)) ℂ),
        A.HoloOn (R.src i) fun x => eval (R.coord i x) h) ∧
      ∀ i, ∀ x ∈ R.src i, ∀ (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ),
        Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
          Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)) →
        ∀ O : Set R.M, IsOpen O → x ∈ O →
          ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
            ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)

theorem AlgRes.exists_atlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e) :
    ∃ A : FinHolAtlas e R.M, R.IsGoodAtlas A := by
  have hloc : ∀ x : R.M, ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ),
      R.GoodChart ψ ∧ x ∈ ψ.source := by
    intro x
    obtain ⟨i, hx⟩ := R.cover x
    obtain ⟨ψ, hψ, hxψ, -⟩ := R.exists_goodChart i x hx (R.sncAt i x hx).r
      (R.sncAt i x hx).span_eq Set.univ isOpen_univ trivial
    exact ⟨ψ, hψ, hxψ⟩
  choose ψ hψ hxψ using hloc
  obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set R.M)).elim_nhds_subcover
    (fun x => (ψ x).source) (fun x _ => (ψ x).open_source.mem_nhds (hxψ x))
  let A : FinHolAtlas e R.M :=
    { n := t.card
      chart := fun j => ψ (t.equivFin.symm j).1
      cover := fun x => by
        obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
        exact ⟨t.equivFin ⟨z, hz⟩, by simpa using hxz⟩
      holo := fun j k => by
        obtain ⟨ik, hsk, ⟨rk, hrk⟩, -⟩ := hψ (t.equivFin.symm k).1
        exact R.analyticOnNhd_comp_symm (hψ _) _ _ (ψ (t.equivFin.symm k).1).open_source ik hsk
          rk hrk }
  have hgood : ∀ j, R.GoodChart (A.chart j) := fun j => hψ _
  refine ⟨A, fun i h j => ?_, fun i x hx r hr O hO hxO => ?_⟩
  · obtain ⟨i', hs, -, g, hg, hgc⟩ := hgood j
    rintro w ⟨hw, hwi⟩
    exact R.analyticAt_coord_symm hs hg hgc i h hw hwi
  · obtain ⟨φ, hφ, hxφ, hsub, hform⟩ := R.exists_goodChart i x hx r hr O hO hxO
    refine ⟨φ, fun j => ⟨?_, ?_⟩, hxφ, hsub, hform⟩
    · exact R.analyticOnNhd_comp_symm (hgood j) φ φ.source φ.open_source i
        (fun y hy => (hsub hy).2) r hform
    · obtain ⟨ij, hsj, ⟨rj, hrj⟩, -⟩ := hgood j
      exact R.analyticOnNhd_comp_symm hφ _ _ (A.chart j).open_source ij hsj rj hrj

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehomA
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

theorem eval₂_mul_const_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (y : σ → S) (t : S) {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n) :
    eval₂ g (fun i => y i * t) f = eval₂ g y f * t ^ n := by
  rw [eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hf (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [Finset.prod_congr rfl (fun i _ => mul_pow (y i) t (d i)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) : f.IsHomogeneous (∑ k, a k) := by
  intro d hd
  have h := hf d (mem_support_iff.2 hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun k _ => h k

theorem prod_update_eq {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p : (k : K) → ι k) (k : K) (v : ι k) :
    ∏ j, x ⟨j, Function.update p k v j⟩ = x ⟨k, v⟩ * ∏ j ∈ Finset.univ.erase k, x ⟨j, p j⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem prod_prod_update {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p p' : (k : K) → ι k) :
    (∏ k, ∏ j, x ⟨j, Function.update p k (p' k) j⟩) * ∏ j, x ⟨j, p j⟩ =
      (∏ k, x ⟨k, p' k⟩) * (∏ j, x ⟨j, p j⟩) ^ Fintype.card K := by
  simp_rw [prod_update_eq x p]
  rw [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun k _ => Finset.prod_erase_mul Finset.univ (fun j => x ⟨j, p j⟩)
    (Finset.mem_univ k)]
  rw [Finset.prod_const, Finset.card_univ]

theorem segreMap_X (p : (k : K) → ι k) :
    segreMap (X p : MvPolynomial ((k : K) → ι k) ℂ) = ∏ k, X ⟨k, p k⟩ := by
  simp [segreMap]

theorem mk_eq_of_segreMap_eq (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    {φ ψ : MvPolynomial ((k : K) → ι k) ℂ} (h : segreMap φ = segreMap ψ) :
    Ideal.Quotient.mk (segreIdeal P) φ = Ideal.Quotient.mk (segreIdeal P) ψ := by
  rw [Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub, h, sub_self]
  exact P.zero_mem

theorem segreW_prod_update [DecidableEq K] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (p p' : (k : K) → ι k) :
    (∏ k, segreW P (Function.update p k (p' k))) * segreW P p =
      segreW P p' * segreW P p ^ Fintype.card K := by
  simp only [segreW, ← map_prod, ← map_mul, ← map_pow]
  apply mk_eq_of_segreMap_eq
  simp only [map_mul, map_prod, map_pow, segreMap_X]
  exact prod_prod_update (X : (Σ k, ι k) → MvPolynomial (Σ k, ι k) ℂ) p p'

theorem segreW_exchange [DecidableEq K] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (p p' : (k : K) → ι k) (q : Σ k, ι k) :
    segreW P (Function.update p q.1 q.2) * segreW P (Function.update p' q.1 (p q.1)) =
      segreW P (Function.update p' q.1 q.2) * segreW P p := by
  obtain ⟨k, v⟩ := q
  simp only [segreW, ← map_mul]
  apply mk_eq_of_segreMap_eq
  simp only [map_mul, segreMap_X]
  rw [prod_update_eq X p k v, prod_update_eq X p' k (p k), prod_update_eq X p' k v,
    ← Finset.mul_prod_erase Finset.univ (fun j => (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (Finset.mem_univ k)]
  ring

theorem segreMap_aeval_update [DecidableEq K] (p : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ}
    {a : K → ℕ} (hf : IsMultiHomog f a) :
    segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * f := by
  have h1 : segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      aeval (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hY : (fun q : Σ k, ι k => segreMap (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) =
      fun q => X q * ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ) := by
    funext q
    rw [segreMap_X, prod_update_eq X p q.1 q.2]
  rw [h1, hY]
  have key : ∀ m ∈ f.support,
      aeval (fun q : Σ k, ι k => X q *
          ∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ))
        (monomial m (f.coeff m)) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) *
        monomial m (f.coeff m) := by
    intro m hm
    have hdeg := hf m hm
    rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    have hc : ∏ q : (Σ k, ι k),
        (∏ j ∈ Finset.univ.erase q.1, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ m q =
        ∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hdeg k]
    rw [hc]
    ring
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  conv_rhs => rw [f.as_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl key

abbrev invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Localization.Away (segreW P p) :=
  Localization.mk 1 ⟨segreW P p, 1, pow_one _⟩

theorem mk_one_mul_invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Localization.mk (segreW P p) 1 * invW P p = 1 := by
  rw [invW, Localization.mk_mul, mul_one, one_mul]
  exact Localization.mk_self (⟨segreW P p, 1, pow_one _⟩ : Submonoid.powers (segreW P p))

theorem mk_pow_eq_mul_invW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (a : MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) (n : ℕ) (h : segreW P p ^ n ∈ Submonoid.powers (segreW P p)) :
    (Localization.mk a ⟨segreW P p ^ n, h⟩ : Localization.Away (segreW P p)) =
      Localization.mk a 1 * invW P p ^ n := by
  rw [invW, Localization.mk_pow, Localization.mk_mul, one_pow, mul_one, one_mul]
  congr 1

theorem eval₂_mk_one {τ : Type} (I : Ideal (MvPolynomial τ ℂ)) (M : Submonoid (MvPolynomial τ ℂ ⧸ I))
    {σ : Type} (Y : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval₂ (algebraMap ℂ (Localization M)) (fun q => Localization.mk (Ideal.Quotient.mk I (Y q)) 1) f =
      Localization.mk (Ideal.Quotient.mk I (aeval Y f)) 1 := by
  simp only [Localization.mk_one_eq_algebraMap]
  have h := MvPolynomial.eval₂_comp_left
    ((algebraMap (MvPolynomial τ ℂ ⧸ I) (Localization M)).comp (Ideal.Quotient.mk I))
    (algebraMap ℂ (MvPolynomial τ ℂ)) Y f
  rw [RingHom.comp_apply] at h
  rw [aeval_def, h]
  congr 1

theorem mul_pow_inv_eq {R : Type*} [CommRing R] (Q W W' t : R) (c : ℕ) (E : Q * W = W' * W ^ c)
    (ht : W * t = 1) : Q * t ^ c = W' * t := by
  calc Q * t ^ c = Q * t ^ c * (W * t) := by rw [ht, mul_one]
    _ = (Q * W) * t ^ c * t := by ring
    _ = W' * (W * t) ^ c * t := by rw [E]; ring
    _ = W' * t := by rw [ht, one_pow, mul_one]

variable [Nonempty K]

theorem segreGrading_algebraMap_surjective {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Function.Surjective (algebraMap ℂ (segreGrading P 0)) := by
  letI := segreGraded hP
  rintro ⟨x, hx⟩
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hx
  have hq' : q.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 q).1 hq
  refine ⟨q.coeff 0, ?_⟩
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap]
  by_cases h0 : q = 0
  · subst h0
    simp
  · have hC : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (hq'.totalDegree h0)
    show _ = (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) q
    nth_rewrite 2 [hC]
    exact ((Ideal.Quotient.mkₐ ℂ _).commutes (q.coeff 0)).symm

theorem segreRing_finiteType {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    letI := segreGraded hP
    Algebra.FiniteType (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) := by
  letI := segreGraded hP
  haveI : Algebra.FiniteType ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (segreIdeal P))
      (Ideal.Quotient.mkₐ_surjective ℂ _)
  haveI : IsScalarTower ℂ (segreGrading P 0) (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [← SetLike.GradeZero.coe_algebraMap (segreGrading P) c]
      rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℂ (segreGrading P 0) _

section Proj

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f := by
  have hg : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι := by
    show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _
    rw [Iso.hom_inv_id_assoc]
  have hB : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero 𝒜 f f_deg hm, ← Category.assoc, hg]
  have h1 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop := by
    rw [Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.appLE_map]
  have h2 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f) ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [h1, ← Scheme.Hom.comp_appTop, hB, Scheme.Hom.comp_appTop]
    have hA : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 f) =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom ≫
          Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv :=
      Proj.basicOpenToSpec_app_top 𝒜 f
    rw [hA]
    rw [← Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  have h3 := (cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).1 h2
  rw [h3, Iso.inv_hom_id_assoc]

end Proj

end

end ReciprocityTheory.AnForm.R
end

