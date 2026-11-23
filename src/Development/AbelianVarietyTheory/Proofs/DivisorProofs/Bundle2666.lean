module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifUnit

theorem prod_unit {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T₀ : Over (Sp R)} (r : T₀ ⟶ T)
    (P : T ⟶ D.P.A) (h : r ≫ P = 1) (χ : D.X) {U : Type} [CommGroup U] (f : (T₀.left ⟶ D.P.A.left) → U) :
    ∏ k, f (r.left ≫ D.Oφ P χ k) ^ Oinvε k = 1 := by
  have e : ∀ k, r.left ≫ D.Oφ P χ k = D.Oφ (1 : T₀ ⟶ D.P.A) χ k := fun k => by
    rw [← h]; exact (WeightPf.Oφ_comp r P χ k).trans rfl
  have e₀ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 0 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 1 :=
    congrArg (fun m : T₀ ⟶ D.P.A => m.left) (_root_.one_mul (toUnit T₀ ≫ D.c χ))
  have e₂ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 2 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 3 := rfl
  simp only [e]
  rw [Fin.prod_univ_four, e₀, e₂]
  simp [Oinvε]

theorem unit_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → (Over.map s).map η[G] ≫ P = 1 → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (eSec G₁)) (LB.oneGen D₁.P.L) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (eSec G₂)) (LB.oneGen D₂.P.L) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec G)) (LB.oneGen D.P.L) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ h₁ h₂ H e u₁ u₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v := H _ (eSec G) y J₁ J₂ J hJ₁ hJ₂ hJ
  have o := prod_unit D ((Over.map s).map η[G]) P e χ (om w y J₁ J₂ J)
  have a₁ : eSec G ≫ σ₁.left = 𝟙 _ ≫ eSec G₁ := (SumDeg.eSec_comp σ₁).trans (Category.id_comp _).symm
  have a₂ : eSec G ≫ σ₂.left = 𝟙 _ ≫ eSec G₂ := (SumDeg.eSec_comp σ₂).trans (Category.id_comp _).symm
  have b₁ : val t₁ (eSec G ≫ σ₁.left) y J₁ = 1 := (congrArg (fun r => val t₁ r y J₁) a₁).trans
    ((val_pull hJ₁ _ _ _).symm.trans ((val_corr hJ₁ u₁ (𝟙 _)).trans (val_one _)))
  have b₂ : val t₂ (eSec G ≫ σ₂.left) y J₂ = 1 := (congrArg (fun r => val t₂ r y J₂) a₂).trans
    ((val_pull hJ₂ _ _ _).symm.trans ((val_corr hJ₂ u₂ (𝟙 _)).trans (val_one _)))
  have c : val t (eSec G) y J = 1 :=
    ((congrArg₂ (· * ·) o rfl).trans (_root_.one_mul _)).symm.trans
      (v.trans ((congrArg₂ (· * ·) b₁ b₂).trans (_root_.one_mul _)))
  exact (val_pull hJ _ _ _).trans ((congrArg (fun r => val t r y J) (Category.id_comp _)).trans
    (c.trans (val_one _).symm))

end GlobalTheory.ProdUnifUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegenerationFirstFactorAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd

theorem adj_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ := by
  intro R _ _ I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂
  obtain ⟨wM, hwM, hrig, hpsi⟩ := hS.w
  have hi₁ : IsMonHom i₁ := _root_.GlobalTheory.isMonHom_section_of_prod_trivial _ _ _ _ p₁ p₂ i₁ hS.hom₁ hS.hom₂ hS.lim e₁ e₂
  have m₁ := _root_.GlobalTheory.MumProd.PsumMap.psum_comp_hom _ _ _ _ 2 p₁ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A]
    ![fst D₁.toPre.P.A D.toPre.P.A, snd D₁.toPre.P.A D.toPre.P.A ≫ p₁] hS.hom₁ (fun i => by
      fin_cases i
      · simp [e₁]
      · simp)
  have m₂ := _root_.GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp _ _ _ _ p₂ ![fst D₁.toPre.P.A D.toPre.P.A ≫ i₁, snd D₁.toPre.P.A D.toPre.P.A] hS.hom₂
    (by simp [e₂])
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.exists_cubeBundle_iso_externalTensor_first_factor _ _ _ _ _ D.toPre.P.L D₁.toPre.P.L D₂.toPre.P.L D.toPre.P.isLB D₁.toPre.P.isLB
    D₂.toPre.P.isLB p₁ p₂ wM hwM _ _ m₁ m₂
  exact ⟨hi₁, hS.hom₁, fun y => _root_.GlobalTheory.MumProd.c_inc_fst _ _ _ _ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y, fun z => (hS.c_pr₁ z).symm, w, hw,
    GlobalTheory.T.periods_sumDegenerationData_fst_cube_iso R I D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ wM hwM hrig hpsi w hval⟩

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstants
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory

theorem isArithVar_charZero_functionField_and_injective :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
      IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  intro k _ X _ p D h
  have hΓ : CharZero Γ(X, ⊤) := h.charZero
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom :=
    germ_injective_of_isIntegral X _ _
  have hK : CharZero X.functionField := (RingHom.charZero_iff hg).1 hΓ
  refine ⟨hK, ?_⟩
  have := h.isDomain
  have := h.finite
  have hint : Algebra.IsIntegral ℤ k := inferInstance
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have : a ∈ RingHom.ker (GlobalTheory.toFunctionField p) := ha
  rw [hker] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithFnField

theorem charZero_and_trdeg_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  intro k _ X _ p D h
  refine ⟨?_, ArithTrdeg.trdeg_functionField_eq h⟩
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
  exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0

end GlobalTheory.ArithFnField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructure
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.IntFib

section Dim

variable {S : Type} [TopologicalSpace S]

theorem dim_le_of_ne_univ [IrreducibleSpace S] {C : Set S} (hC : IsClosed C) (hne : C ≠ Set.univ) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim C ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : C → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  let top : IrreducibleCloseds S := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
  have hlt : q'.last < top := by
    have hsub : (q'.last : Set S) ⊆ C := by
      show closure (Subtype.val '' (q.last : Set C)) ⊆ C
      exact closure_minimal (by rintro _ ⟨t, -, rfl⟩; exact t.2) hC
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
    refine Set.eq_univ_of_univ_subset fun x _ => hsub ?_
    rw [heq]
    exact Set.mem_univ x
  have h1 := Order.LTSeries.length_le_krullDim (q'.snoc top hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

theorem dim_le_of_closedPoint_notMem [T0Space S] [CompactSpace S] {T : Set S}
    (hT : ∀ s : S, IsClosed ({s} : Set S) → s ∉ T) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim T ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : T → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  obtain ⟨t, ht⟩ := q.head.isIrreducible.nonempty
  have htm : (t : S) ∈ (q'.head : Set S) := subset_closure ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hsc⟩ := q'.head.isClosed.exists_closed_singleton ⟨_, htm⟩
  let bot : IrreducibleCloseds S := ⟨{s}, isIrreducible_singleton, hsc⟩
  have hlt : bot < q'.head := by
    refine lt_of_le_of_ne (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) fun heq => ?_
    have : (t : S) ∈ (bot : Set S) := by rw [heq]; exact htm
    have hts : (t : S) = s := this
    exact hT s hsc (hts ▸ t.2)
  have h1 := Order.LTSeries.length_le_krullDim (q'.cons bot hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

end Dim

variable {X : Scheme.{0}}

theorem ringChar_eq_zero_or_prime (x : X) :
    ringChar (X.residueField x) = 0 ∨ (ringChar (X.residueField x)).Prime :=
  (CharP.char_is_prime_or_zero (X.residueField x) _).symm

theorem natCast_eq_zero_iff (ℓ : ℕ) (x : X) :
    (ℓ : X.residueField x) = 0 ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen X x (show x ∈ (⊤ : X.Opens) from trivial)]
  simp

theorem notMem_basicOpen_of_mem_fib {ℓ : ℕ} {x : X} (hx : x ∈ fib X ℓ) :
    x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← natCast_eq_zero_iff, ringChar.spec]
  exact (show ringChar (X.residueField x) = ℓ from hx) ▸ dvd_refl _

theorem mem_fib_iff_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : X) :
    x ∈ fib X ℓ ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  refine ⟨notMem_basicOpen_of_mem_fib, fun h => ?_⟩
  rw [← natCast_eq_zero_iff, ringChar.spec] at h
  rcases hℓ.eq_one_or_self_of_dvd _ h with h1 | h1
  · have h2 : ((1 : ℕ) : X.residueField x) = 0 := (ringChar.spec _ 1).2 (by rw [h1])
    simp at h2
  · exact h1

theorem isClosed_fib {ℓ : ℕ} (hℓ : ℓ ≠ 0) : IsClosed (fib X ℓ) := by
  by_cases hp : ℓ.Prime
  · have e : fib X ℓ = ((X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) : Set X))ᶜ :=
      Set.ext fun x => mem_fib_iff_of_prime hp x
    rw [e]
    exact (X.basicOpen _).isOpen.isClosed_compl
  · have e : fib X ℓ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => by
      have hx' : ringChar (X.residueField x) = ℓ := hx
      rcases ringChar_eq_zero_or_prime x with h | h
      · exact hℓ (hx'.symm.trans h)
      · exact hp (hx' ▸ h)
    rw [e]
    exact isClosed_empty

theorem mem_fib_zero_of_specializes {x y : X} (h : x ⤳ y) (hy : y ∈ fib X 0) : x ∈ fib X 0 := by
  rcases ringChar_eq_zero_or_prime x with h0 | hp
  · exact h0
  · have hx : x ∈ fib X (ringChar (X.residueField x)) := rfl
    have hy' : ringChar (X.residueField y) = ringChar (X.residueField x) :=
      h.mem_closed (isClosed_fib hp.ne_zero) hx
    exact absurd (hy'.symm.trans hy) hp.ne_zero

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {D : ℕ}

theorem fib_ne_univ [IsIntegral X] (hX : IsArithVar p D) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : fib X ℓ ≠ Set.univ := by
  intro h
  have hb : X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) = ⊥ :=
    eq_bot_iff.2 fun x hx => (notMem_basicOpen_of_mem_fib (h.symm ▸ Set.mem_univ x : x ∈ fib X ℓ) hx).elim
  have h0 := (AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hb
  have := hX.charZero
  exact hℓ (Nat.cast_eq_zero.1 h0)

theorem closedPoint_notMem_fib_zero (hX : IsArithVar p D) (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∉ fib X 0 := by
  intro h0
  have := hX.finite_residueField hx
  exact CharP.char_ne_zero_of_finite (X.residueField x) (ringChar (X.residueField x)) h0

theorem fib_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧
      (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧
      (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧
      ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧
        W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  intro k _ X _ p D hX
  have := hX.isNoetherian
  refine ⟨fun x => ?_, fun ℓ hℓ => isClosed_fib hℓ, fun x y h hy => mem_fib_zero_of_specializes h hy,
    fun ℓ => ?_, fun W hW => ?_⟩
  · rcases ringChar_eq_zero_or_prime x with h | h
    · exact .inl h
    · exact .inr ⟨_, h, rfl⟩
  · rcases eq_or_ne ℓ 0 with rfl | hℓ
    · exact dim_le_of_closedPoint_notMem (fun s hs => closedPoint_notMem_fib_zero hX s hs) hX.dim_eq.le
    · exact dim_le_of_ne_univ (isClosed_fib hℓ) (fib_ne_univ hX hℓ) hX.dim_eq.le
  · classical
    obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hW
    let ch : Set X → ℕ := fun t =>
      if h : IsIrreducible t then ringChar (X.residueField (IsIrreducible.genericPoint h)) else 0
    refine ⟨(hTf.toFinset.image ch).filter Nat.Prime, fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2, ?_⟩
    rintro x ⟨t, ht, hxt⟩
    have hct : ch t = ringChar (X.residueField (IsIrreducible.genericPoint (hTi t ht))) := dif_pos (hTi t ht)
    have hg := IsIrreducible.isGenericPoint_genericPoint (hTi t ht) (hTc t ht)
    have hsp := hg.specializes hxt
    rcases ringChar_eq_zero_or_prime (IsIrreducible.genericPoint (hTi t ht)) with h0 | hp
    · left
      exact hsp.mem_closed isClosed_closure (subset_closure ⟨⟨t, ht, hg.mem⟩, h0⟩)
    · right
      refine Set.mem_iUnion₂.2 ⟨ch t, Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨t, hTf.mem_toFinset.2 ht, rfl⟩, hct ▸ hp⟩, ?_⟩
      exact hsp.mem_closed (isClosed_fib (hct ▸ hp.ne_zero)) hct.symm

end GlobalTheory.IntFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T → IsReduced T → t ≫ π = k ≫ spMap (residue R) → ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme), e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧ l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  first | exact @GlobalTheory.Mum.Emb.pullback_iso_of_closed | exact GlobalTheory.Mum.Emb.pullback_iso_of_closed | (intros; apply GlobalTheory.Mum.Emb.pullback_iso_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAddStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_add_chart | exact GlobalTheory.Mum.Conj.secTw_add_chart | (intros; apply GlobalTheory.Mum.Conj.secTw_add_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinearStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) → ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_chart_smul | exact GlobalTheory.Mum.Conj.secTw_chart_smul | (intros; apply GlobalTheory.Mum.Conj.secTw_chart_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), SecTw σ t (secTw A N σ t) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_isTwist | exact GlobalTheory.Mum.Conj.secTw_isTwist | (intros; apply GlobalTheory.Mum.Conj.secTw_isTwist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterTrivialUnitIdeles
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EtaFinUnit

theorem quadChar_finPartI_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ b : Neutral.B1.Ideles (maximalRealSubfield E),
    b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (GlobalTheory.GalOfCusp.quadChar E).1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 := by
  intro E _ _ _ hU b hb
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) (GlobalTheory.GalOfCusp.quadChar E).1
    (GlobalTheory.GalOfCusp.quadChar E).2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hb) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hb v
  obtain ⟨w, rfl⟩ := hs v
  exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt E w (hU w) x hxu

end GlobalTheory.EtaFinUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem upAtPrime_groups_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  intro k _ X _ p P u a b
  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      Real.exp (-(a * ((upperParabolic P u).L.φ σ).φ (pick ((upperParabolic P u).L.φ σ).isLB y) y + b * ((upperParabolic P u).A.φ σ).φ (pick ((upperParabolic P u).A.φ σ).isLB y) y) / 2)
        = Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)
          * Real.exp (-(a * u.u σ y) / 2) := by
    intro σ y
    rw [← Real.exp_add]
    congr 1
    show -(a * ((P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + u.u σ y) + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 = _
    ring
  refine ⟨rfl, fun f => rfl, fun σ y f => ⟨?_, ?_⟩⟩
  · show ratVal _ y * ((Real.exp _ : ℝ) : ℂ) = ratVal _ y * ((Real.exp _ : ℝ) : ℂ) * _
    rw [key σ y, Complex.ofReal_mul, mul_assoc]
    rfl
  · show ‖ratVal _ y‖ * Real.exp _ = ‖ratVal _ y‖ * Real.exp _ * _
    rw [key σ y, mul_assoc]
    rfl

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_values_tensor_data_matrix_action : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  first | exact @GlobalTheory.Mum.TensRos.rosGt_values | exact GlobalTheory.Mum.TensRos.rosGt_values | (intros; apply GlobalTheory.Mum.TensRos.rosGt_values <;> assumption)
end

