module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GmCharPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertySemiAbelianFlatBaseChangeDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussBC

theorem gp_comp_eq_spMap_cst : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R),
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  intro X _ R _ p
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_regAt_zeroAt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X), p x = closedPoint R → ∀ r : R, GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  intro R _ _ X _ p x hx r
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.GaussBC

namespace GlobalTheory.Desc.GaussBC

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem zero_mem_spanBy (T : Set F₁) : (0 : F₁) ∈ spanBy c T := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy {T : Set F₁} {v w : F₁} (hv : v ∈ spanBy c T) (hw : w ∈ spanBy c T) :
    v + w ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem mul_mem_spanBy {T : Set F₁} {v : F₁} (hv : v ∈ spanBy c T) (d : R₁) : c d * v ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  exact ⟨n, fun i => d * r i, t, ht, by rw [Finset.mul_sum]; simp only [map_mul, _root_.mul_assoc]⟩

theorem spanBy_induction {T : Set F₁} (p : F₁ → Prop) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ r, ∀ t ∈ T, p (c r * t)) : ∀ v ∈ spanBy c T, p v := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact Finset.sum_induction _ p hadd h0 fun i _ => hmul (r i) (t i) (ht i)

end Span

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem gauss_baseChange : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmT := hϖ.maximalIdeal_eq
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]

  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_eq_spMap_cst H.left T H.hom
    have e2 := gp_comp_eq_spMap_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  set c := cst H'.hom with hc
  set P := c (a ϖ) with hPdef
  have hP : P = θ (cst H.hom ϖ) := by rw [hPdef, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply]
  obtain ⟨hϖ0, hfac⟩ := _root_.GlobalTheory.Desc.GenFibre.unif T H hH y hy hdy ϖ hmT
  have hP0 : P ≠ 0 := by rw [hP]; exact (map_ne_zero θ).2 hϖ0
  have hPz : GlobalTheory.Cartier.ZeroAt y' P :=
    (cst_regAt_zeroAt D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := _root_.GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_regAt_zeroAt D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_regAt_zeroAt T H.left H.hom y hy t).1
  have hmod := _root_.GlobalTheory.Desc.ModPi.modPi T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy' ϖ hmT
  set S := spanBy c (θ '' regSet y) with hS
  have hSreg : ∀ v ∈ S, GlobalTheory.Cartier.RegAt y' v :=
    spanBy_induction c _ (regAt_zero y') (fun _ _ h h' => h.add h') (by
      rintro r _ ⟨t, ht, rfl⟩; exact (hcreg r).mul (hreg t ht))
  have hSP : ∀ v ∈ S, ∀ N : ℕ, P ^ N * v ∈ S := by
    intro v hv N
    induction N with
    | zero => simpa using hv
    | succ N ih => rw [pow_succ', _root_.mul_assoc]; exact mul_mem_spanBy c ih _

  have hQ : ∀ v ∈ spanBy c (Set.range θ), ∃ N : ℕ, P ^ N * v ∈ S := by
    refine spanBy_induction c _ ⟨0, by simpa using zero_mem_spanBy c _⟩ ?_ ?_
    · rintro v w ⟨N, hN⟩ ⟨M, hM⟩
      refine ⟨N + M, ?_⟩
      have := add_mem_spanBy c (hSP _ hN M) (hSP _ hM N)
      convert this using 1; ring
    · rintro r _ ⟨u, rfl⟩
      by_cases hu : u = 0
      · exact ⟨0, by simpa [hu] using zero_mem_spanBy c _⟩
      obtain ⟨k, w, hw, rfl⟩ := hfac u hu
      refine ⟨(-k).toNat, ?_⟩
      have hk : ((-k).toNat : ℤ) + k = ((((-k).toNat : ℤ) + k).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      have e : P ^ (-k).toNat * (c r * θ (cst H.hom ϖ ^ k * w)) =
          c r * θ (cst H.hom ϖ ^ (((-k).toNat : ℤ) + k).toNat * w) := by
        rw [hP, map_mul, map_mul, map_zpow₀, map_pow]
        have hq : θ (cst H.hom ϖ) ^ (-k).toNat * θ (cst H.hom ϖ) ^ k =
            θ (cst H.hom ϖ) ^ (((-k).toNat : ℤ) + k).toNat := by
          rw [← zpow_natCast, ← zpow_natCast _ (((-k).toNat : ℤ) + k).toNat, ← hk,
            zpow_add₀ ((map_ne_zero θ).2 hϖ0)]
        linear_combination (c r * θ w) * hq
      rw [e]
      exact mul_mem_spanBy c (subset_spanBy c (θ '' regSet y) (Set.mem_image_of_mem θ
        (show _ ∈ regSet y from (regAt_pow (hc0reg ϖ) _).mul hw.regAt))) r

  have hB : ∀ (N : ℕ) (t : H'.left.functionField), GlobalTheory.Cartier.RegAt y' t → P ^ N * t ∈ S → t ∈ S := by
    intro N
    induction N with
    | zero => intro t _ h; simpa using h
    | succ N ih =>
      intro t ht h
      rw [pow_succ', _root_.mul_assoc] at h
      obtain ⟨z₁, hz₁, e⟩ := hmod _ h (hPz.mul ((regAt_pow hPz.regAt N).mul ht))
      have : P ^ N * t = z₁ := mul_left_cancel₀ hP0 e
      exact ih t ht (this ▸ hz₁)
  refine ⟨fun v ⟨d, hd0, hdv⟩ => ⟨fun hv => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hQ _ hdv
    have hirr : Irreducible (a ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmD
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
    have e : P ^ (N + n) * v = c (↑u⁻¹ : D) * (P ^ N * (c (↑u * a ϖ ^ n) * v)) := by
      rw [hPdef, map_mul, map_pow]
      have : c (↑u⁻¹ : D) * c ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(c (a ϖ) ^ (N + n) * v)) * this
    refine ⟨1, fun h => (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [map_one, _root_.one_mul]
    exact hB (N + n) v hv (e ▸ mul_mem_spanBy c hN _)
  · obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hs
    have e : v = c (↑u⁻¹ : D) * (c ↑u * v) := by rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e]; exact (hcreg _).mul (hSreg _ hsv)
  · ext u
    refine ⟨fun h => ?_, fun h => hreg u h⟩
    change GlobalTheory.Cartier.RegAt y' (θ u) at h
    change GlobalTheory.Cartier.RegAt y u
    by_cases hu : u = 0
    · rw [hu]; exact regAt_zero y
    obtain ⟨k, w, hw, rfl⟩ := hfac u hu
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [zpow_natCast]; exact (regAt_pow (hc0reg ϖ) k).mul hw.regAt
    · exfalso
      have hw0 := hw.ne_zero
      obtain ⟨hw1, hw2⟩ := (unitAt_iff hw0).1 hw
      have hθw : GlobalTheory.Cartier.UnitAt y' (θ w) :=
        (unitAt_iff ((map_ne_zero θ).2 hw0)).2 ⟨hreg w hw1, by rw [← map_inv₀]; exact hreg _ hw2⟩
      have hm1 : ((-(k + 1)).toNat : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
      have e : P⁻¹ = θ (cst H.hom ϖ ^ k * w) * (θ w)⁻¹ * P ^ (-(k + 1)).toNat := by
        rw [map_mul, map_zpow₀, ← hP, _root_.mul_assoc (P ^ k), mul_inv_cancel₀ ((map_ne_zero θ).2 hw0),
          _root_.mul_one, ← zpow_natCast, hm1, ← zpow_add₀ hP0, show k + -(k + 1) = -1 by ring, zpow_neg_one]
      have hPi : GlobalTheory.Cartier.RegAt y' P⁻¹ := by
        rw [e]; exact (h.mul hθw.inv.regAt).mul (regAt_pow hPz.regAt _)
      exact (zeroAt_iff.1 hPz).2 ((unitAt_iff hP0).2 ⟨hPz.regAt, hPi⟩)
  · exact _root_.GlobalTheory.Desc.FlatLin.linDisj_of_flat T D a ha H H' π θ hpb ⟨_, hff.choose_spec⟩

end GlobalTheory.Desc.GaussBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericallyFiniteFiniteNearCodimOnePoint
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.PushFinite

theorem coheight_genericPoint (X : Scheme.{0}) [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.2 fun b _ => genericPoint_specializes b

theorem dim_closure_add_one_le {X : Scheme.{0}} {a b : X} (hab : a < b) :
    topologicalKrullDim (closure ({a} : Set X)) + 1 ≤ topologicalKrullDim (closure ({b} : Set X)) := by
  refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure
    fun x hx => ⟨b, subset_closure rfl, fun hb => ?_, ?_⟩
  · exact hab.not_ge (specializes_iff_mem_closure.2 hb)
  · have h1 : b ⤳ a := hab.le
    have h2 : a ⤳ x := specializes_iff_mem_closure.2 hx
    exact h1.trans h2

theorem finite_notMem_coheight_le_one {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : {ξ : X | ξ ∉ U ∧ Order.coheight ξ ≤ 1}.Finite := by
  obtain ⟨S, hS, hcl, hirr, hun⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  have hg : genericPoint X ∈ U := (genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem
  refine (hS.biUnion (t := fun C => {κ | IsGenericPoint κ C}) fun C _ =>
    Set.Subsingleton.finite fun _ h _ h' => h.eq h').subset ?_
  rintro ξ ⟨hξ, h1⟩
  obtain ⟨C, hC, hξC⟩ : ξ ∈ ⋃₀ S := hun ▸ hξ
  obtain ⟨κ, hκ⟩ := QuasiSober.sober (hirr C hC) (hcl C hC)
  have hκU : κ ∈ (U : Set X)ᶜ := hun ▸ ⟨C, hC, hκ.mem⟩
  refine Set.mem_biUnion hC ?_
  by_cases h : ξ ⤳ κ
  · rwa [(h.antisymm (hκ.specializes hξC)).eq]
  · have hlt : ξ < κ := lt_of_le_not_ge (hκ.specializes hξC) h
    have hlt' : κ < genericPoint X := lt_of_le_not_ge (genericPoint_specializes κ)
      fun h' => hκU (((genericPoint_specializes κ).antisymm h').eq ▸ hg)
    have h2 := (add_le_add_left (le_add_self.trans (Order.coheight_add_one_le hlt')) 1).trans
      ((Order.coheight_add_one_le hlt).trans h1)
    exact absurd h2 (by decide)

theorem isFinite_restrict_of_le {X Y : Scheme.{0}} (g : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    [IsFinite (g ∣_ U)] : IsFinite (g ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsFinite ((g ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  haveI : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{0}) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun f g e hf => by
      have : IsFinite g.hom := by
        rw [← Arrow.inv_left_hom_right e.hom]
        infer_instance
      exact this
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict g U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq g e)).1 h1

theorem finite_near_coheight_one : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ z : X, Order.coheight z = 1 → (g ⁻¹' {z}).Finite ∧ (∀ w : Y, g w = z → Order.coheight w = 1) ∧ ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧ IsFinite (g ∣_ V) := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη hd z hz
  obtain ⟨hbX1, -, hbX3, -, -, hbX6⟩ := _root_.GlobalTheory.MixHt.hasDim_basic k X p hp
  obtain ⟨hbY1, -, -, -, -, hbY6⟩ := _root_.GlobalTheory.MixHt.hasDim_basic k Y q hq
  obtain ⟨mX, hmX⟩ := hbX1
  obtain ⟨mY, hmY⟩ := hbY1
  obtain ⟨n, -, hnY⟩ := hmY (genericPoint Y)
  obtain ⟨nX, -, hnX⟩ := hmX (genericPoint X)
  have hnn : n = nX :=
    ((_root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg (genericPoint Y) n nX hnY (hη ▸ hnX)).2).1 hd
  subst hnn
  have hzne : z ≠ genericPoint X := by
    rintro rfl
    rw [coheight_genericPoint] at hz
    exact zero_ne_one hz
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := by
    rcases n with _ | e
    · exfalso
      have hcl := (hbX3 (genericPoint X)).1 hnX
      have huniv : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
      rw [hcl.closure_eq] at huniv
      have : z ∈ ({genericPoint X} : Set X) := huniv ▸ Set.mem_univ z
      exact hzne this
    · exact ⟨e, rfl⟩
  have hXd : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) := (hbX6 X (e + 1)).1 hnX
  have hYd : topologicalKrullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞) := (hbY6 Y (e + 1)).1 hnY
  obtain ⟨hoX, -⟩ := _root_.GlobalTheory.MixHt.dimOne k X p hp e hXd
  obtain ⟨hoY, -⟩ := _root_.GlobalTheory.MixHt.dimOne k Y q hq e hYd
  have hze : HasDim z e := (hoX z).1 hz
  have hw : ∀ w : Y, g w = z → Order.coheight w = 1 := by
    intro w hwz
    rw [hoY]
    obtain ⟨dw, -, hdw⟩ := hmY w
    have h1 : e ≤ dw := (_root_.GlobalTheory.DimDeg.dim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg w dw e hdw (hwz ▸ hze)).1
    have hwne : w ≠ genericPoint Y := by
      rintro rfl
      exact hzne (hwz.symm.trans hη)
    have hlt := dim_closure_add_one_le (lt_of_le_not_ge (genericPoint_specializes w)
      fun h' => hwne ((genericPoint_specializes w).antisymm h').eq.symm)
    unfold HasDim at hdw hnY
    rw [hdw, hnY] at hlt
    have h2 : dw + 1 ≤ e + 1 := by exact_mod_cast hlt
    have : dw = e := le_antisymm (by omega) h1
    subst this
    exact hdw
  have hfin : (g ⁻¹' {z}).Finite := by
    haveI := hq.isNoetherian
    let U : Y.Opens := g ⁻¹ᵁ ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : genericPoint Y ∈ U := by
      show g (genericPoint Y) ∈ (closure ({z} : Set X))ᶜ
      rw [hη]
      intro hc
      exact hzne ((specializes_iff_mem_closure.2 hc).antisymm (genericPoint_specializes z)).eq
    refine (finite_notMem_coheight_le_one U ⟨_, hU⟩).subset fun w hwz => ⟨fun hwU => ?_, (hw w hwz).le⟩
    have hwU' : g w ∈ (closure ({z} : Set X))ᶜ := hwU
    exact hwU' (by rw [show g w = z from hwz]; exact subset_closure rfl)
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (g ≫ p) := hg ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper g := IsProper.of_comp g p
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton g z hfin
  obtain ⟨V, hV, hzV, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hzV₀
  exact ⟨hfin, hw, V, hV, hzV, isFinite_restrict_of_le g hle⟩

end GlobalTheory.PushFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmCharHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifWeight

open ReciprocityTheory.ChartRestriction.G.DVR

section Char

variable {S : Scheme.{0}} {X X₁ X₂ : Type} [AddCommGroup X] [AddCommGroup X₁] [AddCommGroup X₂]

theorem gm_char_hom {j : X₁ → X} {τ : splitTorus S X ⟶ splitTorus S X₁} (hτ : TorusHomOf j τ) {T : Over S}
    (r : T ⟶ splitTorus S X) (y : T.left) (x : X₁) :
    gm (r ≫ τ).left y ⊤ (charUnit S X₁ x) = gm r.left y ⊤ (charUnit S X (j x)) := by
  rw [← hτ x]
  exact ((gm_res r.left y (V := ⊤) _ trivial _).trans (gm_pull r.left τ.left y ⊤ trivial _)).symm

theorem gm_char_add {T : Over S} (r : T ⟶ splitTorus S X) (y : T.left) (a b : X) :
    gm r.left y ⊤ (charUnit S X (a + b)) = gm r.left y ⊤ (charUnit S X a) * gm r.left y ⊤ (charUnit S X b) := by
  rw [PowTorusCoord.gm_char, PowTorusCoord.gm_char, PowTorusCoord.gm_char, ofAdd_add, map_mul, map_mul]

end Char

theorem val_weight {R : Type} [CommRing R] [IsDomain R] {D₁ : DegPre R} {S : Scheme.{0}} {s : S ⟶ Sp R}
    {X : Type} [AddCommGroup X] {G G₁ : Over S} [GrpObj G] [GrpObj G₁] (σ : G ⟶ G₁) [IsMonHom σ]
    {P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A} {x : D₁.X} (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ x) Oinvε))
    (κ : splitTorus S X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (τ : splitTorus S X ⟶ splitTorus S D₁.X)
    (hκ : κ ≫ σ = τ ≫ κ₁)
    (hw : LB.Gen.Corr D₁.P.L _ _ _ _
      (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left)
      (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L x)
        (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)))
    (y : (splitTorus S X ⊗ G).left) {J} (hJ : Good D₁.P.L y J) :
    val (Y := G₁.left) t₁ ((lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ).left y J =
      gm (fst (splitTorus S X) G ≫ τ).left y ⊤ (charUnit _ D₁.X x) *
        val (Y := G₁.left) t₁ (snd (splitTorus S X) G ≫ σ).left y J := by
  let N : splitTorus S X ⊗ G ⟶ splitTorus S D₁.X ⊗ G₁ := τ ⊗ₘ σ
  have n₁ : N ≫ fst _ _ = fst _ _ ≫ τ := tensorHom_fst _ _
  have n₂ : N ≫ snd _ _ = snd _ _ ≫ σ := tensorHom_snd _ _
  have n₃ : N ≫ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]) =
      (lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ := by
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, n₁, n₂, Category.assoc,
      Category.assoc, hκ]
  rw [← n₁, ← n₂, ← n₃]
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ hw N.left).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))

theorem weight_box₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → ∀ (κ : splitTorus S D.X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (κ₂ : splitTorus S D₂.X ⟶ G₂) (j₁ : D₁.X → D.X) (j₂ : D₂.X → D.X) (τ₁ : splitTorus S D.X ⟶ splitTorus S D₁.X) (τ₂ : splitTorus S D.X ⟶ splitTorus S D₂.X), j₁ (q₁ χ) + j₂ (q₂ χ) = χ → TorusHomOf j₁ τ₁ → TorusHomOf j₂ τ₂ → κ ≫ σ₁ = τ₁ ≫ κ₁ → κ ≫ σ₂ = τ₂ ≫ κ₂ → (Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ P = (Over.map s).map (snd (splitTorus S D.X) G) ≫ P → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left) (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L (q₁ χ)) (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (lift (fst (splitTorus S D₂.X) G₂ ≫ κ₂) (snd _ _) ≫ μ[G₂]).left) (LB.mulGen D₂.P.L _ _ _ _ (charGen D₂.X G₂ D₂.P.L (q₂ χ)) (LB.pullGen D₂.P.L _ _ t₂ (snd (splitTorus S D₂.X) G₂).left)) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left) (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L χ) (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ hσ₁ hσ₂ H κ κ₁ κ₂ j₁ j₂ τ₁ τ₂ hχ
    hτ₁ hτ₂ hκ₁ hκ₂ aO hw₁ hw₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v₁ := val_weight σ₁ t₁ κ κ₁ τ₁ hκ₁ hw₁ y hJ₁
  have v₂ := val_weight σ₂ t₂ κ κ₂ τ₂ hκ₂ hw₂ y hJ₂
  rw [gm_char_hom hτ₁] at v₁
  rw [gm_char_hom hτ₂] at v₂
  have c := gm_char_add (fst (splitTorus S D.X) G) y (j₁ (q₁ χ)) (j₂ (q₂ χ))
  rw [hχ] at c
  have b₁ := H _ (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := H _ (snd (splitTorus S D.X) G).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have e : ∀ a, (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a =
      (snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a := fun a =>
    (WeightPf.Oφ_comp ((Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G])) P χ a).trans
      ((congrArg (fun m => D.Oφ m χ a) aO).trans
        (WeightPf.Oφ_comp ((Over.map s).map (snd (splitTorus S D.X) G)) P χ a).symm)
  have o : (∏ a, om w y J₁ J₂ J ((lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a) ^ Oinvε a) =
      ∏ a, om w y J₁ J₂ J ((snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a) ^ Oinvε a :=
    Finset.prod_congr rfl fun a _ => congrArg (fun m => om w y J₁ J₂ J m ^ Oinvε a) (e a)
  have v₄ := (congrArg₂ (· * ·) o rfl).symm.trans (b₁.trans ((congrArg₂ (· * ·) v₁ v₂).trans
    ((_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg₂ (· * ·) c.symm b₂.symm).trans (mul_left_comm _ _ _)))))
  have v₅ := mul_left_cancel v₄
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅

end GlobalTheory.ProdUnifWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem loc_fields_near : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ (x : A.Pt) (k : ℕ), ∀ᶠ v in 𝓝 x.crd, A.loc (fld A (powFld A G k)) x.1.1 v = powAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (fld A (chernFld A G k)) x.1.1 v = chernAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (transFld A G G' k) x.1.1 v = transAt (fun u => G x.pt (x.ch.symm u)) (fun u => G' x.pt (x.ch.symm u)) v k := by
  intro M _ n A r _ _ G G' hG x k
  obtain ⟨⟨i, y⟩, hy⟩ := x
  have hyt : A.e i y ∈ (A.e i).target := (A.e i).map_source hy
  have hsymm : (A.e i).symm (A.e i y) = y := (A.e i).left_inv hy
  have hcont : Tendsto (A.e i).symm (𝓝 (A.e i y)) (𝓝 y) := by
    have := (A.e i).continuousAt_symm hyt
    rwa [ContinuousAt, hsymm] at this
  obtain ⟨⟨hGu, hGs⟩, ⟨hG'u, hG's⟩⟩ := hG.smooth y
  have e1 := hGs i hy
  have e2 := hG's i hy
  have u1 := e1.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hGu)
  have u2 := e2.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hG'u)
  filter_upwards [(A.e i).open_target.mem_nhds hyt, hcont.eventually (hG.trans y), e1, e2, u1, u2]
    with v hv htr h1 h2 h3 h4
  obtain ⟨T, K, K', hT, hK, hK', hw⟩ := htr
  have hz : (A.e i).symm v ∈ (A.e i).source := (A.e i).map_target hv
  have hzv : A.e i ((A.e i).symm v) = v := (A.e i).right_inv hv
  have hct : Tendsto (A.e i).symm (𝓝 v) (𝓝 ((A.e i).symm v)) := (A.e i).continuousAt_symm hv
  have dT := hT.2 i hz
  have dK := hK.2 i hz
  have dK' := hK'.2 i hz
  rw [hzv] at dT dK dK'
  have key := _root_.GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame n r (fun u => G y ((A.e i).symm u)) (fun u => G' y ((A.e i).symm u))
    (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
    (fun u => T ((A.e i).symm u)) (fun u => K ((A.e i).symm u)) (fun u => K' ((A.e i).symm u)) v
    h1 h3 h2 h4 dT hT.1 dK hK.1 dK' hK'.1 (hct.eventually hw) k
  refine ⟨?_, ?_, ?_⟩
  · rw [HolAtlas.loc, dite_eq_left hv]
    show ((powAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.1]
  · rw [HolAtlas.loc, dite_eq_left hv]
    show ((chernAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.2.1]
  · rw [HolAtlas.loc, dite_eq_left hv]
    show transAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
      (A.e i ((A.e i).symm v)) k = _
    rw [hzv, key.2.2]

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrobeniusKernelIdealOfZeroDifferentialStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], ∀ b : H, counit (R := K) b = 0 → dUnit (R := K) b = 0 → Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0 → b ∈ frobKerIdeal p K H := by
  first | exact @GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne | exact GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne | (intros; apply GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne <;> assumption)
end

