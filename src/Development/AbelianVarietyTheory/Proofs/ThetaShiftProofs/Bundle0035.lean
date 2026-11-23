module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecialisedPointsHolomorphicQuasiPeriodic
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecHol

open Filter Topology GlobalTheory.Specialise GlobalTheory.HolHom GlobalTheory.CoordFamily

theorem ev_comb_factor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ lin cst, IsFactor A lin cst → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw la v, Conv.ev T w hw (f (v + A.Pw w la)) = Complex.exp (lin w la v + cst w la) ^ j * Conv.ev T w hw (f v) := by
  intro O _ _ A lin cst hF
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ f hf w hw la v => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : ∀ z, Conv.ev T w hw (f z) =
      ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w z := by
    intro z
    have hm : ∀ i, A.FSum j (α i) (th i) z ∈ Conv.halfRing T :=
      fun i _ hw' => (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw' z).summable
    have hv : ∀ i, Conv.ev T w hw ⟨_, hm i⟩ = A.Sum j (α i) (th i) w z :=
      fun i => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum (h₀.mono hT) (h1 i).2 hw z)
    have e : f z = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact h2 z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i]
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF.sum w la v j (α i) (th i) (h1 i).2]
  ring

theorem of_coords (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H)
    (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B)
    (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ)
    (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (hF : IsFactor A lin cst) (N : ℕ) [NeZero N]
    (C : Coords Φ N) :
    ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → (∀ z, HolAt (fun v => (Ψ.pi w v).left) z) ∧
      (∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v) ∧
      (∀ j z, ⊤ ≤ (Ψ.pi w z).left ⁻¹ᵁ o.t.PP.L.U j → DifferentiableAt ℂ (fun v => Ψ.fr w j v ^ N) z) ∧
      ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
        Ψ.fr w j v ^ N = (Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la)) ^ N := by
  obtain ⟨T₁, hT₁, hC, h₁⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ N C
  obtain ⟨T₂, h₂⟩ := GlobalTheory.ArcPts.exists_formal_convergence _ A
  obtain ⟨T₃, h₃⟩ := ev_comb_factor _ A lin cst hF
  set T := max T₁ (max T₂ T₃) with hT
  have e₁ : T₁ ≤ T := le_max_left _ _
  have e₂ : T₂ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have e₃ : T₃ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, le_trans hT₁ e₁, fun w hw => ?_⟩
  have hw₁ : T₁ < w.im := e₁.trans_lt hw
  have hwC : C.T < w.im := hC.trans_lt hw₁
  have hwΨ : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw₁
  obtain ⟨hy, -, hval⟩ := h₁ w hw₁
  let f : Fin C.n → A.V → Conv.halfRing T := fun i v => Subalgebra.inclusion (Conv.halfRing_mono (hC.trans e₁)) (C.cf i v)
  have hf : ∀ i, IsComb A N (Conv.halfRing T) (fun v => f i v) := fun i => by
    obtain ⟨n, r, α, th, h, h'⟩ := C.comb i
    exact ⟨n, r, α, th, fun a => ⟨Conv.halfRing_mono (hC.trans e₁) (h a).1, (h a).2⟩, h'⟩
  let c : Fin C.n → A.V → ℂ := fun i v => Conv.ev C.T w hwC (C.cf i v)
  have hcf : ∀ i v, c i v = Conv.ev T w hw (f i v) := fun i v => Conv.ev_congr hwC hw rfl
  have hd : ∀ i, Differentiable ℂ (c i) := fun i => by
    rw [show c i = fun v => Conv.ev T w hw (f i v) from funext (hcf i)]
    exact (h₂ T e₂ N).2 (f i) (hf i) w hw
  have hp : ∀ la v i, c i (v + A.Pw w la) = Complex.exp (lin w la v + cst w la) ^ N * c i v := fun la v i => by
    rw [hcf, hcf]
    exact h₃ T e₃ N (f i) (hf i) w hw la v
  have hfr := (SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hwΨ).2.2.1
  have hex : ∀ v, ∃ x : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme, x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left := fun v => by
    have hxU : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
      rw [← Scheme.Hom.comp_preimage, Over.w]
      exact hy
    exact ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.pi w v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  choose x hx using hex
  have hv : ∀ i v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR (x v) ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
        c i v * Ψ.fr w j v ^ N := fun i v j hj => hval i v (x v) j (hx v) hj
  have hc : ∀ v, HasCoords (x v) C.b fun i => c i v := fun v => hasCoords_powOver o.t.PP.isLB fun j hj => by
    rw [hx] at hj
    exact ⟨((hfr v).1 j hj).unit ^ N, fun i => by simpa using hv i v j hj⟩
  have hi : (o.t.G.hom ∣_ C.U) ≫ C.U.ι = (o.t.G.hom ⁻¹ᵁ C.U).ι ≫ o.t.G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (o.t.G.hom ∣_ C.U) = x 0 ≫ (o.t.G.hom ∣_ C.U) := fun v => by
    rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, hi, ← Category.assoc, ← Category.assoc, hx, hx,
      Over.w, Over.w]
  have hhol : ∀ z, HolAt x z := fun z => holAt_of_coords C.emb hy' hc fun i => hd i z
  have hhol' : ∀ z, HolAt (fun v => (Ψ.pi w v).left) z := fun z => by
    have := (hhol z).comp (o.t.G.hom ⁻¹ᵁ C.U).ι
    simpa only [hx] using this
  have hper : ∀ la v, x v = x (v + A.Pw w la) := fun la v =>
    eq_of_proportional C.emb ((hy' _).trans (hy' _).symm) (hc v) (hc _) (hp la v)
  have hper' : ∀ la v, Ψ.pi w (v + A.Pw w la) = Ψ.pi w v := fun la v =>
    Over.OverMorphism.ext (by rw [← hx, ← hx, ← hper])
  refine ⟨hhol', hper', fun j z hj => ?_, fun la v j hj => ?_⟩
  · obtain ⟨i, hi0⟩ := C.bpf w hwC z
    have hzj : ⊤ ≤ x z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
      intro p _
      rw [← hx] at hj
      exact Set.mem_iInter.2 fun _ => hj (x := p) trivial
    have h1 := (hhol z _ hzj).2 ((C.b i).f (fun _ => j))
    have hne : ∀ᶠ v in 𝓝 z, c i v ≠ 0 := (hd i z).continuousAt.eventually_ne hi0
    refine (h1.fun_mul ((hd i z).fun_inv hi0)).congr_of_eventuallyEq
      (((hhol' z _ hj).1.and hne).mono fun v hv' => ?_)
    simp only [valAt'_eq_valR]
    rw [hv i v j hv'.1, mul_comm, inv_mul_cancel_left₀ hv'.2]
  · obtain ⟨i, hi0⟩ := C.bpf w hwC v
    have h1 := hv i v j hj
    have h2 := hv i (v + A.Pw w la) j (by rw [hper']; exact hj)
    rw [← hper, h1, hp] at h2
    apply mul_left_cancel₀ (show c i v ≠ 0 from hi0)
    rw [h2]
    ring

theorem specPts_holomorphic : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → IsHolTo Set.univ (fun v => (Ψ.pi w v).left) ∧ (∀ la, Ψ.pi w (A.Pw w la) = 1) ∧ (∀ j, DifferentiableOn ℂ (Ψ.fr w j) {v | ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j}) ∧ ∀ la v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v = Complex.exp (lin w la v + cst w la) * Ψ.fr w j (v + A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ lin cst hF
  obtain ⟨C₄⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C₅⟩ := GlobalTheory.SpanFrame.nonempty_coords hL hL2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  obtain ⟨T₄, hT₄, h₄⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 4 C₄
  obtain ⟨T₅, -, h₅⟩ := of_coords E H D l B bb S s o A y Φ Γ Ψ lin cst hF 5 C₅
  refine ⟨max T₄ T₅, le_max_of_le_left hT₄, fun w hw => ?_⟩
  have hw₄ : T₄ < w.im := (le_max_left _ _).trans_lt hw
  obtain ⟨hhol, hper, hd₄, hq₄⟩ := h₄ w hw₄
  obtain ⟨-, -, hd₅, hq₅⟩ := h₅ w ((le_max_right _ _).trans_lt hw)
  obtain ⟨hadd, -, hfr, -⟩ := SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w (lt_of_le_of_lt hT₄ hw₄)
  have hne : ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j v ≠ 0 := fun v j hj => ((hfr v).1 j hj).ne_zero
  refine ⟨isHolTo_of_holAt isOpen_univ fun z _ => hhol z, fun la => ?_, fun j z hz => ?_, fun la v j hj => ?_⟩
  · have h := hper la 0
    rw [hadd] at h
    exact mul_eq_left.1 h
  · refine DifferentiableAt.differentiableWithinAt ?_
    refine ((hd₅ j z hz).fun_mul ((hd₄ j z hz).fun_inv (pow_ne_zero _ (hne z j hz)))).congr_of_eventuallyEq
      ((hhol z _ hz).1.mono fun v hv => ?_)
    have := hne v j hv
    beta_reduce
    field_simp
  · have h := hq₅ la v j hj
    rw [pow_succ _ 4, pow_succ _ 4, ← hq₄ la v j hj] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (hne v j hj)) h

end GlobalTheory.SpecHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDeriv
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecTangent

open TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R') (h : ∀ r, ρ (inl r) = inl (φ r))
    (he : ρ DualNumber.eps = DualNumber.eps) : ρ = dualMapR φ := by
  refine RingHom.ext fun a => ?_
  have e : a = inl a.fst + inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add (f := _), map_mul, h, h, he]
  ext <;> simp [dualMapR]

theorem dualMapR_add (φ : R →+* R') (a b : R) : dualMapR φ (inl a + inr b) = inl (φ a) + inr (φ b) := by
  ext <;> simp [dualMapR]

theorem dualMapR_comp (φ : R →+* R') :
    (dualMapR φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem base_dualMapR {R₀ : Type} [CommRing R₀] (ψ : R₀ →+* R) (φ : R →+* R') {Z : Scheme.{0}} (y : Sp R₀ ⟶ Z) :
    spMap (dualMapR φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ spMap ψ ≫ y =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap (φ.comp ψ) ≫ y := by
  rw [← Category.assoc, ← spMap_comp, dualMapR_comp, spMap_comp _ (algebraMap R' _), spMap_comp ψ, Category.assoc,
    Category.assoc]

theorem dualMapR_injective {φ : R →+* R'} (h : Function.Injective φ) : Function.Injective (dualMapR φ) := by
  intro a b e
  ext
  · exact h (by simpa [dualMapR] using congrArg fst e)
  · exact h (by simpa [dualMapR] using congrArg snd e)

theorem isLocalRing_dual [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [isUnit_iff_isUnit_fst, fst_sub, fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem isLocalHom_dualMapR (φ : R →+* R') [IsLocalHom φ] : IsLocalHom (dualMapR φ) :=
  ⟨fun a ha => isUnit_iff_isUnit_fst.2 (IsUnit.of_map φ _ (by
    simpa [dualMapR] using isUnit_iff_isUnit_fst.1 ha))⟩

theorem le_of_isLocalHom [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] {Z : Scheme.{0}}
    (x : Sp R ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint R') trivial
  rw [← IsLocalRing.comap_closedPoint φ]
  exact this

end Dual

theorem exists_lift_open {X Z : Scheme.{0}} (x : X ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ z : X ⟶ U.toScheme, z ≫ U.ι = x :=
  ⟨IsOpenImmersion.lift U.ι x (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact h (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_sec_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {K : Type} [CommRing K] {y : Sp K ⟶ S} (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ h : pullback G.hom y ⟶ (G.hom ⁻¹ᵁ U).toScheme, h ≫ (G.hom ⁻¹ᵁ U).ι = pullback.fst _ _ ∧
      ∀ b : LB.Sec (Out.powOver G L U N), ∃ s : SecP L (pullback.fst G.hom y) N,
        ∀ (R : Type) [CommRing R] (q : Sp R ⟶ pullback G.hom y) (j : L.ι), ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ L.U j →
          valR (q ≫ h) ((Out.powOver G L U N).U (fun _ => j)) (b.f (fun _ => j)) = sval s q j := by
  obtain ⟨h, e⟩ := exists_lift_open (pullback.fst G.hom y) (G.hom ⁻¹ᵁ U) (by
    rw [← Scheme.Hom.comp_preimage, pullback.condition]
    exact SpecCoord.comp_le_preimage _ _ _ hy)
  refine ⟨h, e, fun b => ?_⟩
  obtain ⟨s, hs, -⟩ := AmpleSpan.existsUnique_secScal hL (φ := fun _ : Fin N => (G.hom ⁻¹ᵁ U).ι) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => pullback.fst G.hom y) (ε' := fun _ => (N : ℤ)) (h := h)
    (AmpleSpan.formEq_const e (by simp)) b
  exact ⟨s, fun R _ q j hj => SpanFrame.valR_of_secScal e hs q j hj⟩

theorem exists_deriv_comb {O : Type} [CommRing O] [StarRing O] (A : AnArc O) : ∃ T₀ : ℝ, ∀ (T T₁ : ℝ) (hT : T ≤ T₁),
    T₀ ≤ T₁ → ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) →
    ∀ z₀ : A.V, ∃ (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ)
      (F : Fin n → ℂ⸨X⸩) (d : Conv.halfRing T₁), (∀ i, th i ∈ A.Theta j (α i)) ∧
      (∀ v, (f v : ℂ⸨X⸩) = ∑ i, r i * A.FSum j (α i) (th i) v) ∧ (∀ i, IsDFSum A j (α i) (th i) z₀ (F i)) ∧
      (d : ℂ⸨X⸩) = ∑ i, r i * F i ∧ ∀ w (hw : T₁ < w.im),
        Differentiable ℂ (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) ∧
        Conv.ev T₁ w hw d = fderiv ℂ (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) 0 z₀ := by
  obtain ⟨T₀, h₀⟩ := exists_formal_convergence O A
  refine ⟨T₀, fun T T₁ hT hT₀ j _ f hf z₀ => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  obtain ⟨hS, hD⟩ := h₀ T₁ hT₀ j
  choose hm hv using fun i => (hS (α i) (th i) (h1 i).2).1
  choose F hF hFv using fun i => (hS (α i) (th i) (h1 i).2).2 z₀
  let r₁ : Fin n → Conv.halfRing T₁ := fun i => ⟨r i, Conv.halfRing_mono hT (h1 i).1⟩
  refine ⟨n, r, α, th, fun i => F i, ∑ i, r₁ i * F i, fun i => (h1 i).2, h2, hF,
    AddSubmonoidClass.coe_finsetSum _ _, fun w hw => ?_⟩
  have hd : ∀ i, Differentiable ℂ (A.Sum j (α i) (th i) w) := fun i => by
    have := hD (fun v => ⟨_, hm i v⟩) ⟨1, fun _ => 1, fun _ => α i, fun _ => th i,
      fun _ => ⟨one_mem _, (h1 i).2⟩, fun v => by simp⟩ w hw
    simpa only [hv] using this
  have key : (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) =
      fun v => ∑ i, Conv.ev T₁ w hw (r₁ i) * A.Sum j (α i) (th i) w v := by
    funext v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Conv.ev_congr (hT.trans_lt hw) hw (s' := ∑ i, r₁ i * ⟨_, hm i v⟩)
      (by rw [AddSubmonoidClass.coe_finsetSum]; exact h2 v), map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv]
  rw [key]
  refine ⟨Differentiable.fun_sum fun i _ => (hd i).const_mul _, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fderiv_fun_sum fun i _ => ((hd i).const_mul _) 0, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hFv, fderiv_const_mul (hd i 0)]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y}

theorem exists_coords_tan {N : ℕ} [NeZero N] (C : Coords Φ N) {z₀ : A.V}
    {ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y} (hν : Φ.IsTan z₀ ν) :
    ∃ (T₁ : ℝ) (hT : C.T ≤ T₁) (d : Fin C.n → Conv.halfRing T₁)
      (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ (t.G.hom ⁻¹ᵁ C.U).toScheme), ν' ≫ (t.G.hom ⁻¹ᵁ C.U).ι = ν ≫ pullback.fst _ _ ∧
      (∀ j, ⊤ ≤ (ν ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U j → ∃ u : (DualNumber ℂ⸨X⸩)ˣ, ∀ i,
        valR ν' ((Out.powOver t.G t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
          (inl (C.cf i 0 : ℂ⸨X⸩) + inr (d i : ℂ⸨X⸩)) * (u : DualNumber ℂ⸨X⸩)) ∧
      ∀ i w (hw : T₁ < w.im), Differentiable ℂ (fun v => Conv.ev C.T w (hT.trans_lt hw) (C.cf i v)) ∧
        Conv.ev T₁ w hw (d i) = fderiv ℂ (fun v => Conv.ev C.T w (hT.trans_lt hw) (C.cf i v)) 0 z₀ := by
  obtain ⟨T₀, h₀⟩ := exists_deriv_comb A
  choose n r α th F d hth hf hF hd hev using
    fun i => h₀ C.T (max C.T T₀) (le_max_left _ _) (le_max_right _ _) N (C.cf i) (C.comb i) z₀
  obtain ⟨h, e, hs⟩ := exists_sec_fibre (N := N) t.PP.isLB C.mem
  obtain ⟨h1, -, τ, hτ, hval⟩ := hν
  refine ⟨_, le_max_left _ _, d, ν ≫ h, by rw [Category.assoc, e], fun j hj => ⟨(hτ.1 j hj).unit ^ N, fun i => ?_⟩, hev⟩
  obtain ⟨s, hs⟩ := hs (C.b i)
  have hx : ∀ v, fib (Φ.x v) ≫ pullback.fst t.G.hom y = (Φ.x v).left := fun v => pullback.lift_fst _ _ _
  rw [hs _ ν j hj, sval_eq_sum_of_hasVal E H S A t y Φ N s (n i) (r i) (α i) (th i) (hth i) (fun v k hk => by
    rw [← hs _ _ k hk, ← hf]
    exact C.val i v _ k (by rw [Category.assoc, e, hx]) (hx v ▸ hk)) _ _ ν h1 j hj, hf, hd,
    Units.val_pow_eq_pow_val, IsUnit.unit_spec, inl_sum, inr_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hval N _ _ (hth i k) _ (hF i k) j hj, ← _root_.mul_assoc]
  congr 1
  ext1 <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_tangent : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  intro hL hL₂ E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ z₀ ν hν
  obtain ⟨C⟩ := _root_.GlobalTheory.SpanFrame.nonempty_coords hL hL₂ E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨T₁, hT₁, d, ν', eν, hc, hd⟩ := exists_coords_tan C hν
  obtain ⟨T₂, hT₂, hT₃, hs⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ 4 C
  refine ⟨max T₁ T₂, le_max_of_le_right hT₂, fun w hw hw' => ?_⟩
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw'
  have hwC : C.T < w.im := hT₁.trans_lt hw₁
  obtain ⟨hy, hg, hv⟩ := hs w ((le_max_right _ _).trans_lt hw')
  haveI := ArcSectionValue.isLocalRing_germ Γ w
  haveI := isLocalRing_dual (R := Γ.R w)
  haveI := o.proper
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  haveI := isLocalHom_dualMapR (Γ.ev w).toRingHom
  obtain ⟨j, hj⟩ := ArcSectionValue.exists_chart_local (ν ≫ pullback.fst o.t.G.hom y) o.t.PP.isLB
  obtain ⟨u, hu⟩ := hc j hj
  obtain ⟨i₀, hi₀⟩ := C.bpf w hwC 0
  obtain ⟨x, ⟨x1, x2, x3⟩, -⟩ := _root_.GlobalTheory.LiftPoint.existsUnique_lift S o.t.G o.t.PP.L C.U 4 C.n C.b (DualNumber (Γ.R w)) (DualNumber ℂ⸨X⸩)
    (dualMapR (Γ.R w).val.toRingHom)
    (spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫
      spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ν'
    (fun i => inl (Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i 0)) +
      inr (Subalgebra.inclusion (Γ.le T₁ w hw₁) (d i))) j u o.t.PP.isLB C.aff C.emb
    (dualMapR_injective Subtype.val_injective) (SpecCoord.comp_le_preimage _ _ _ (hg hw))
    (by
      rw [reassoc_of% eν, pullback.condition, reassoc_of% hν.1, base_dualMapR]
      exact congrArg _ Ψ.yT_gen.symm)
    (eν ▸ hj) (fun i => by rw [hu, dualMapR_add]; rfl)
    ⟨i₀, isUnit_iff_isUnit_fst.2 (by
      rw [fst_add, fst_inl, fst_inr, add_zero]
      exact Γ.unit w _ (by rwa [Γ.ev_eq]))⟩
  refine ⟨x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι, (Category.assoc _ _ _).trans x1, fun ρ h he => ?_, fun ρ h he => ?_⟩
  · rw [eq_dualMapR (Γ.R w).val.toRingHom ρ h he, reassoc_of% x2, eν]
  obtain rfl := eq_dualMapR (Γ.ev w).toRingHom ρ h he
  choose p hp using fun v => exists_lift_open (Ψ.pi w v).left (o.t.G.hom ⁻¹ᵁ C.U) (by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hy)
  have key := ((coords_determine_family S o.t.G o.t.PP.L C.U 4 C.n C.b (Ψ.yw w) A.V p
    (fun i v => Conv.ev C.T w hwC (C.cf i v)) o.t.PP.isLB C.aff C.emb
    (fun v => by rw [reassoc_of% hp v]; exact Over.w _)
    (fun v k hk => by
      rw [hp] at hk
      refine ⟨Ψ.fr w k v ^ 4, pow_ne_zero _ ?_, fun i => hv i v _ k (hp v) hk⟩
      refine (((Ψ.τt_frm w hw v).1 k (SpecCoord.germ_le_preimage Γ w _ _ ?_)).map (Γ.ev w)).ne_zero
      rwa [← Ψ.pi_eq w hw v])).2 fun i => (hd i w hw₁).1).2 z₀ (spMap (dualMapR (Γ.ev w).toRingHom) ≫ x)
    (by
      rw [Category.assoc, x1, base_dualMapR, Ψ.yw_eq w hw]
      congr 3
      exact RingHom.ext fun r => Γ.ev_eq Ψ.T w hw r)
    (fun k hk => by
      rw [Category.assoc] at hk
      have hk' := le_of_isLocalHom _ _ hk
      obtain ⟨u', hu'⟩ := x3 k hk'
      set_option synthInstance.maxHeartbeats 200000 in
      refine ⟨Units.map (dualMapR (Γ.ev w).toRingHom).toMonoidHom u', fun i => ?_⟩
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U 4).U (fun _ => k) :=
        fun z hz => Set.mem_iInter.2 fun _ => hk' hz
      rw [HolHom.valR_spMap _ _ _ hx, hu', map_mul, dualMapR_add,
        ← (hd i w hw₁).2, ← Γ.ev_eq, ← Γ.ev_eq]
      rfl)
  simp only [hp, Category.assoc] at key
  refine ⟨?_, fun W f hW => (key W f).2 hW⟩
  rw [← hp 0, ← (key ⊤ 0).1, Category.assoc, Category.assoc]

end GlobalTheory.SpecTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ThetaAllFibres

theorem exists_mem_of_flat {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (U : X.Opens) {x : X} (hx : p x = IsLocalRing.closedPoint R) (hU : x ∈ U) (g : Sp R) :
    ∃ y : X, p y = g ∧ y ∈ U := by
  have hs : g ⤳ p x := hx ▸ IsLocalRing.specializes_closedPoint (R := R) g
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap p hs
  exact ⟨y, e, hy.mem_open U.isOpen hU⟩

theorem mem_nonzeroLocus_of_h0Sec {X : Scheme.{0}} {L : LB X} {σ : Out.H0 L 1} {θ : LB.Sec L} (h : SectionOfLineBundleOne σ θ) {x : X}
    (hx : x ∈ Out.nonzeroLocus σ) : x ∈ Out.nonzeroLocus θ := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun y hy => Set.mem_iInter.1 hy 0
  rw [h j le] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, hj.2⟩

theorem nonzeroLocus_eq_of_heq {S : Scheme.{0}} {G : Over S} [GrpObj G] {L L' : RigLB G} (e : L' = L)
    {θ : LB.Sec L.L} {θ' : LB.Sec L'.L} (h : HEq θ θ') : Out.nonzeroLocus θ = Out.nonzeroLocus θ' := by
  subst e
  rw [eq_of_heq h]

theorem X_notMem_or_eq_closedPoint {A : Type} [CommRing A] [IsLocalRing A] (hA : IsField A)
    (g : PrimeSpectrum (PowerSeries A)) :
    PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A) := by
  refine or_iff_not_imp_left.2 fun h => ?_
  rw [not_not] at h
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal g.isPrime.ne_top) fun f hf => ?_)
  have h₀ : PowerSeries.constantCoeff f = 0 := by
    by_contra hne
    obtain ⟨b, hb⟩ := hA.mul_inv_cancel hne
    exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal f).1 hf))
      (PowerSeries.isUnit_iff_constantCoeff.2 (IsUnit.of_mul_eq_one b hb))
  obtain ⟨q, rfl⟩ := PowerSeries.X_dvd_iff.2 h₀
  exact g.asIdeal.mul_mem_right _ h

theorem theta_nonzero_on_fibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L), ThNZ th → ThetaOf W th θ → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ g : Sp (PowerSeries A), (IsField A → PowerSeries.X ∉ g.asIdeal ∨ g = IsLocalRing.closedPoint (PowerSeries A)) ∧ ∃ x : W.t.G.left, W.t.G.hom x = g ∧ x ∈ Out.nonzeroLocus θ := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th θ hth hθ _ g
  refine ⟨fun hA => X_notMem_or_eq_closedPoint hA g, ?_⟩
  obtain ⟨σ, fam, θ', hE, hp, h0, he⟩ := hθ
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ IsLocalRing.maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have := W.t.semi.geomConnected
  have := W.P.U.smooth
  obtain ⟨σ₀, -, -, -, -, hu, -, hz⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange hI W.P.U (fam 0)
    ((GlobalTheory.ThetaUnit.existsUnique_pullTerm W th).2 (fam 0) hp hth _)
  obtain rfl := hu σ fam rfl hE
  obtain ⟨x, hx, hn⟩ := (hz σ 1 ((GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 (one_smul _ _).symm)).2.1 isUnit_one
  rw [nonzeroLocus_eq_of_heq W.P.bundle he]
  exact exists_mem_of_flat W.t.G.hom _ hx (mem_nonzeroLocus_of_h0Sec h0 hn) g

end GlobalTheory.ThetaAllFibres
end

