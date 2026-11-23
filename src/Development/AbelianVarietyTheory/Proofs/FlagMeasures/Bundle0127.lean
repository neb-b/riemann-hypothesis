module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassProduct

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

theorem uniformiser_mem_jacobson (ϖ : 𝒪[F]) (h : Irreducible ϖ) (w : L.O)
    (hw : (w : E) = algebraMap F E (ϖ : F)) : w ∈ (⊥ : Ideal L.O).jacobson := by
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O
    (fun x => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := f.toAlgebra
  haveI : IsScalarTower 𝒪[F] L.O E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral 𝒪[F] L.O := by
    refine ⟨fun x => ?_⟩
    have h1 : IsIntegral 𝒪[F] (x : E) := (L.O_def (x : E)).1 x.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] L.O E) Subtype.val_injective).1 h1
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨-, hP⟩
  haveI := hP
  have hmax : (P.comap (algebraMap 𝒪[F] L.O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝒪[F]) P
  have hm : ϖ ∈ P.comap (algebraMap 𝒪[F] L.O) := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal _).2 h.not_isUnit
  have he : algebraMap 𝒪[F] L.O ϖ = w := by
    apply Subtype.ext
    rw [hw]
    rfl
  rw [Ideal.mem_comap, he] at hm
  exact hm

theorem stabilises_of_close {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (hΛ : Λ.FG) (ϖ : 𝒪[F])
    (h : Irreducible ϖ) (m : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hm : ∀ x ∈ Λ, ∃ y ∈ Λ, m x - x = algebraMap F E (ϖ : F) • y) :
    m ∈ MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ := by
  have hO : algebraMap F E (ϖ : F) ∈ L.O := (L.O_def _).2 (by
    have : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E ϖ) := isIntegral_algebraMap
    exact this)
  let w : L.O := ⟨_, hO⟩
  have hw : w ∈ (⊥ : Ideal L.O).jacobson := uniformiser_mem_jacobson L ϖ h w rfl
  have hle : m • Λ ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := hm x hx
    have : m x = x + w • y := by
      rw [eq_add_of_sub_eq' e]
      rfl
    change m x ∈ Λ
    rw [this]
    exact Λ.add_mem hx (Λ.smul_mem w hy)
  have hge : Λ ≤ m • Λ := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {w}) hΛ
      ((Ideal.span_singleton_le_iff_mem _).2 hw) ?_
    intro x hx
    obtain ⟨y, hy, e⟩ := hm x hx
    have hx' : x = m x - w • y := by
      have : m x = x + w • y := by
        rw [eq_add_of_sub_eq' e]
        rfl
      rw [this]; abel
    rw [hx']
    refine Submodule.sub_mem_sup ?_ ?_
    · exact Submodule.smul_mem_pointwise_smul x m Λ hx
    · exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self w) hy
  exact MulAction.mem_stabilizer_iff.2 (le_antisymm hle hge)

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable (A : Places F E sig) (n : ℕ)

def extMap (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose

theorem extMap_spec (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    A.Ext p g (extMap A n g p) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.1

theorem extMap_unique {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {p : HeightOneSpectrum (𝓞 F)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g') :
    g' = extMap A n g p :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.2 g' h

def extHom : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →*
    ∀ p, (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) where
  toFun g := extMap A n g
  map_one' := funext fun p => (extMap_unique A n (g := 1) (g' := 1) fun _ => rfl).symm
  map_mul' a b := funext fun p => (extMap_unique A n (g := a * b)
    (g' := extMap A n a p * extMap A n b p) (fun x => by
      change extMap A n a p (extMap A n b p (A.bc p x)) = A.bc p (a (b x))
      rw [extMap_spec A n b p x, extMap_spec A n a p (b x)])).symm

theorem comap_pi (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    (Subgroup.pi Set.univ K).comap (extHom A n) = A.rat K := by
  ext g
  constructor
  · intro h p
    exact ⟨extMap A n g p, (Subgroup.mem_pi _).1 h p (Set.mem_univ p), extMap_spec A n g p⟩
  · intro h
    refine (Subgroup.mem_pi _).2 fun p _ => ?_
    obtain ⟨g', hg, he⟩ := h p
    have e : extMap A n g p = g' := (extMap_unique A n he).symm
    change extMap A n g p ∈ K p
    rw [e]
    exact hg

end Global

theorem mass_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k →
    ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ →
    {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧
      G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, hcoord⟩ := _root_.GlobalTheory.HL.PlacesRec.lattice_local A (k + 2 * r + 1) Λ hΛ
  have hstd := _root_.GlobalTheory.HL.StdPlace.coordinate_lattice_standard A r k G hk
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hfin : {p | U p ≠ K p}.Finite := by
    refine (hstd.union hcoord).subset ?_
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hp
    change (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) = (G.S p).K0
    rw [h2]
    exact h1.2.2.1
  have hKSt : ∀ p, K p ≤ (G.S p).St := fun p x hx => hx.1.1
  have hUSt : ∀ p, U p ≤ (G.S p).St := fun p x hx => hx.1

  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p =>
    if U p ≠ K p then
      haveI := (A.loc p).lf
      Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
        (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0))
    else 1
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hfin.subset ?_
    intro p hp
    by_contra hcon
    apply hp
    have hu : U p = K p := not_not.1 hcon
    have h1 : c p = 1 := if_neg (not_not.2 hu)
    exact ⟨1, by rw [h1]; simp⟩
  let φ := extHom A (k + 2 * r + 1)
  have hdense : ∀ g, g ∈ Subgroup.pi Set.univ K ∨ g ∈ Subgroup.pi Set.univ U →
      ∃ γ, (φ γ)⁻¹ * g ∈ Subgroup.pi Set.univ K ⊓ Subgroup.pi Set.univ U := by
    intro g hg
    have hgSt : ∀ p, g p ∈ (G.S p).St := by
      intro p
      rcases hg with h | h
      · exact hKSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · exact hUSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
    have hgfin : {p | g p ∉ (G.S p).K0}.Finite := by
      rcases hg with h | h
      · refine Set.finite_empty.subset ?_
        intro p hp
        exact hp ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · refine hfin.subset ?_
        intro p hp he
        apply hp
        have := (Subgroup.mem_pi _).1 h p (Set.mem_univ p)
        rw [he] at this
        exact this
    have happrox := by
      first
      | exact _root_.GlobalTheory.HL.StrongSt.strong_approx_stab A r k G Λ hΛ c hc g hgSt hgfin
      | exact _root_.GlobalTheory.HL.StrongSt.strong_approx_stab A r k G Λ hΛ.toIsLattice c hc g hgSt hgfin
    obtain ⟨γ, -, hγ⟩ := happrox
    refine ⟨γ, ?_⟩
    have key : ∀ p, (g p)⁻¹ * φ γ p ∈ K p ⊓ U p := by
      intro p
      obtain ⟨h1, h2⟩ := hγ p (φ γ p) (extMap_spec A _ γ p)
      refine ⟨h1, ?_⟩
      by_cases he : U p = K p
      · rw [he]; exact h1
      · refine ⟨hKSt p h1, ?_⟩
        haveI := (A.loc p).lf
        have hcp : ((c p : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
          have h3 : c p = Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
              (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0)) := if_pos he
          rw [h3]
          rfl
        refine stabilises_of_close (A.L p) (A.lat p Λ) (hlat p).1 (G.S p).ϖ (G.S p).ϖ_irr _ ?_
        intro x hx
        obtain ⟨y, hy, e⟩ := h2 x hx
        refine ⟨y, hy, ?_⟩
        rw [← hcp]
        exact e
    have key2 : ∀ p, ((φ γ)⁻¹ * g) p ∈ K p ⊓ U p := by
      intro p
      have := (K p ⊓ U p).inv_mem (key p)
      simpa [mul_inv_rev] using this
    exact ⟨(Subgroup.mem_pi _).2 fun p _ => (key2 p).1, (Subgroup.mem_pi _).2 fun p _ => (key2 p).2⟩
  obtain ⟨hKU, hUK⟩ := _root_.GlobalTheory.HL.relIndex_pair_comap_of_dense_image φ (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) hdense
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU' : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨-, -, hprod⟩ := _root_.GlobalTheory.HL.invVol_pi_univ K U hKU' hidx
  refine ⟨hfin, ?_⟩
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (comap_pi A _ U).symm
  have hmu : G.mu Λ = invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) := by
    unfold GFrames.mu invVol
    rw [e1, e2, hKU, hUK]
  rw [hmu, hprod]
  rfl

end GlobalTheory.HL.MassProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharIffCoord
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.IndChar

theorem isChar_iff_coord {G : Type} [Group G] (χ : G → ℂ) :
    GlobalTheory.GLq.IsChar χ ↔ GlobalTheory.BI.IsChar ℂ ℂ χ := by
  constructor
  · rintro ⟨V, hV⟩

    let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
    refine ⟨Module.finrank ℂ V, GlobalTheory.BI.transportRep V.ρ e, fun g => ?_⟩
    rw [GlobalTheory.BI.character_transportRep, ← hV g]
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨FDRep.of ρ, fun g => ?_⟩
    rw [hρ g]
    rfl

theorem isChar_induced : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ), IsChar φ → IsChar (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G, if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) := by
  intro G _ _ H φ hφ

  have hind : GlobalTheory.BI.IsChar ℂ ℂ (GlobalTheory.BI.ind H φ) :=
    GlobalTheory.BI.isChar_ind ℂ ℂ G H φ ((isChar_iff_coord φ).mp hφ)
  have heq : (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G,
      if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) = GlobalTheory.BI.ind H φ := by
    funext x
    unfold GlobalTheory.BI.ind
    rw [finsum_eq_sum_of_fintype]
    congr 1
  rw [heq]
  exact (isChar_iff_coord _).mpr hind

end GlobalTheory.GLm.IndChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharTraceOfMul
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem isChar_trace_of_mul {M V : Type} [Group M] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : M → Module.End ℂ V) (hT : ∀ a b, T (a * b) = T a * T b) :
    IsChar (fun m => LinearMap.trace ℂ V (T m)) := by
  have hmem : ∀ m v, T m v ∈ LinearMap.range (T 1) := fun m v =>
    ⟨T m v, by rw [← Module.End.mul_apply, ← hT, one_mul]⟩
  let ρ : Representation ℂ M (LinearMap.range (T 1)) :=
    { toFun := fun m => (T m).restrict (fun v _ => hmem m v)
      map_one' := by
        refine LinearMap.ext ?_
        rintro ⟨_, v, rfl⟩
        refine Subtype.ext ?_
        show T 1 (T 1 v) = T 1 v
        rw [← Module.End.mul_apply, ← hT, one_mul]
      map_mul' := fun a b => by
        refine LinearMap.ext fun v => Subtype.ext ?_
        show T (a * b) v = T a (T b v)
        rw [hT]; rfl }
  refine ⟨FDRep.of ρ, fun m => ?_⟩
  exact LinearMap.trace_restrict_eq_of_forall_mem _ (T m) (hmem m) (fun v _ => hmem m v)

theorem sum_fibre_one {P M : Type} [Group P] [Fintype P] [Group M] (π : P →* M) (hπ : Function.Surjective π)
    (m : M) : (∑ x : P, if π x = m then (1 : ℂ) else 0) = (Nat.card π.ker : ℂ) := by
  obtain ⟨x₀, rfl⟩ := hπ m
  rw [← Equiv.sum_comp (Equiv.mulLeft x₀)]
  simp only [Equiv.coe_mulLeft, map_mul, mul_eq_left]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MonoidHom.mem_ker]

theorem isChar_fibre_mean : ∀ (P M : Type) [Group P] [Fintype P] [Group M] [Fintype M] (π : P →* M) (χ : P → ℂ),
    Function.Surjective π → IsChar χ →
    IsChar (fun m : M => (Nat.card π.ker : ℂ)⁻¹ * ∑ x : P, if π x = m then χ x else 0) := by
  intro P M _ _ _ _ π χ hπ ⟨V, hV⟩
  have hc : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let S : M → Module.End ℂ V := fun m => ∑ x : P, if π x = m then V.ρ x else 0
  have hS : ∀ a b, S a * S b = (Nat.card π.ker : ℂ) • S (a * b) := by
    intro a b
    rw [← sum_fibre_one π hπ a, Finset.sum_smul]
    simp only [S]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : π x = a
    · rw [if_pos hx, if_pos hx, one_smul, Finset.mul_sum,
        ← Equiv.sum_comp (Equiv.mulLeft x) (fun y => if π y = a * b then V.ρ y else 0)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Equiv.coe_mulLeft, map_mul, hx, mul_right_inj]
      split_ifs <;> simp
    · rw [if_neg hx, if_neg hx, zero_mul, zero_smul]
  have h := isChar_trace_of_mul (fun m => (Nat.card π.ker : ℂ)⁻¹ • S m) (fun a b => by
    rw [smul_mul_smul_comm, hS, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one])
  convert h using 2 with m
  rw [map_smul, smul_eq_mul]
  congr 1
  simp only [S]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [← hV]; rfl
  · simp

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepCompHomAndMul
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem isChar_comp_hom {G M : Type} [Group G] [Group M] (π : G →* M) (χ : M → ℂ)
    (h : IsChar χ) : IsChar (fun x => χ (π x)) := by
  obtain ⟨V, hV⟩ := h
  exact ⟨FDRep.of (V.ρ.comp π), fun x => hV (π x)⟩

theorem isChar_mul_fun {G : Type} [Group G] (α β : G → ℂ) (hα : IsChar α) (hβ : IsChar β) :
    IsChar (fun x => α x * β x) := by
  obtain ⟨V, hV⟩ := hα
  obtain ⟨W, hW⟩ := hβ
  refine ⟨CategoryTheory.MonoidalCategoryStruct.tensorObj V W, fun x => ?_⟩
  rw [FDRep.char_tensor, Pi.mul_apply, hV, hW]

theorem isChar_comp_hom_and_mul :
    (∀ (G M : Type) [Group G] [Group M] (π : G →* M) (χ : M → ℂ),
      IsChar χ → IsChar (fun x => χ (π x))) ∧
    ∀ (G : Type) [Group G] (α β : G → ℂ), IsChar α → IsChar β → IsChar (fun x => α x * β x) :=
  ⟨fun _ _ _ _ π χ h => isChar_comp_hom π χ h, fun _ _ α β hα hβ => isChar_mul_fun α β hα hβ⟩

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepMemCyclotomicAdjoin
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem trace_mem_adjoin_of_pow_eq_one (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (N : ℕ) (hN : 0 < N) (hf : f ^ N = 1) :
    LinearMap.trace ℂ V f ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine multiset_sum_mem _ ?_
  intro μ hμ
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf] at h1
  have h2 : μ ^ N = 1 := by
    have h3 : (μ ^ N - 1) • v = 0 := by
      rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one h2
  rw [← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

theorem isChar_mem_adjoin_exp :
    ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ →
      ∀ x, χ x ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  intro G _ _ χ N hN hd hχ x
  obtain ⟨V, hV⟩ := hχ
  rw [← hV x]
  refine trace_mem_adjoin_of_pow_eq_one V (V.ρ x) N hN ?_
  obtain ⟨k, rfl⟩ := hd
  rw [← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTrivialPointwise
section
open NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NearLowerCompare

open Formalism.MainNotions.S GlobalTheory.Count Formalism.HN

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)

end General

variable (I : AutInst)

theorem lamX_isLattice (x : I.GA) : Submodule.IsLattice I.E (lamX I x) := by
  have h := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg) I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  have e : lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
    ext y
    rw [GlobalTheory.Count.Test.mem_lamX, ← e1]
    exact Iff.rfl
  rw [e]; exact h

theorem frm_isUnit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h : ∀ v, IsUnit (I.P v * uMat (x.1 v)) := fun v => (I.P_unit v).mul (Units.isUnit _)
  rw [← Matrix.isUnit_iff_isUnit_det]
  unfold frm
  split_ifs
  · exact h _
  · exact (h _).map (starRingEnd ℂ).mapMatrix

theorem subsingleton_GA (hn : I.n = 0) : Subsingleton I.GA := by
  have : IsEmpty (Fin I.n) := by rw [hn]; infer_instance
  refine ⟨fun a b => Prod.ext (funext fun v => ?_) ?_⟩
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

end GlobalTheory.NearLowerCompare
end
end

