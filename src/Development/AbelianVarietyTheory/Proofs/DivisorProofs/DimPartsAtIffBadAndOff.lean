module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf LevelP P0)
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.SumWCompare
open scoped TensorProduct

namespace GlobalTheory.DimPartsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

variable {D : D7}

theorem star_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def cPl (w : Pl D.host.E) : Pl D.host.E :=
  ⟨w.asIdeal.comap (cj D.host.E), haveI := w.isPrime; Ideal.comap_isPrime _ _, fun h0 => w.ne_bot (by
    rw [eq_bot_iff]
    intro x hx
    have : cj _ x ∈ w.asIdeal.comap (cj D.host.E) := by rwa [Ideal.mem_comap, cj_cj]
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← cj_cj x, this, map_zero])⟩

theorem mem_cPl (w : Pl D.host.E) (x : 𝓞 D.host.E) : x ∈ (cPl w).asIdeal ↔ cj _ x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : Pl D.host.E) : cPl (cPl w) = w := HeightOneSpectrum.ext (by ext x; rw [mem_cPl, mem_cPl, cj_cj])

theorem isConjPl_cPl (w : Pl D.host.E) : Formalism.BasicNotions.IsConjPl D.host w (cPl w) := by
  intro x y hxy
  have : y = cj _ x := RingOfIntegers.ext (hxy.trans (star_conj _).symm)
  rw [mem_cPl, this, cj_cj]

theorem plGw_ne_cPl (k : Fin 2) (v v' : D.nd.PlG k) : D.naut.plGw k v ≠ cPl (D.naut.plGw k v') := fun e =>
  D.naut.plGw_nconj k v' v (e ▸ isConjPl_cPl _)

theorem g_mem_plGw (k : Fin 2) (v : D.nd.PlG k) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal :=
  D.naut.plGw_over k v

theorem cover (k : Fin 2) (w : Pl D.host.E) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = cPl (D.naut.plGw k v) := by
  let f : D.nd.PlG k ⊕ D.nd.PlG k → Formalism.BasicNotions.placesOver D.host.E (D.host.g k) :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, g_mem_plGw k v⟩) fun v => ⟨cPl (D.naut.plGw k v), by
      show cj _ _ ∈ (D.naut.plGw k v).asIdeal
      rw [map_natCast]; exact g_mem_plGw k v⟩
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · rw [D.naut.plGw_inj k e']
    · exact absurd e' (plGw_ne_cPl k a b)
    · exact absurd e'.symm (plGw_ne_cPl k b a)
    · have := congrArg cPl e'
      simp only [f, Sum.elim_inr, cPl_cPl] at this
      rw [D.naut.plGw_inj k this]
  have hE : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [h1, h5]; ring
  have hc : Nat.card (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)) = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, D.nd.g_split k, hE, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, D.nd.g_split k]
    exact Module.finrank_pos.ne'
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · exact ⟨v, Or.inr (congrArg Subtype.val hx).symm⟩

def PlaceTie (D : D7) : Prop :=
  ∃ pb : Fin 2 → 𝓞 D.host.E, ∀ k, (pb k : D.host.E) ∈ D.host.K ∧
    (pb k : D.host.E) * star (pb k : D.host.E) = (D.host.g k : D.host.E) ∧ ∀ v, pb k ∈ (D.naut.plGw k v).asIdeal

def OnePrime (D : D7) : Prop :=
  ∀ k v v', (D.naut.plGw k v).under (𝓞 D.host.K) = (D.naut.plGw k v').under (𝓞 D.host.K)

def below (k : Fin 2) (v : D.nd.PlG k) : LevelCuspCharacters.PlOver D.host k :=
  ⟨(D.naut.plGw k v).under (𝓞 D.host.F), by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (D.naut.plGw k v).asIdeal
    rw [map_natCast]; exact g_mem_plGw k v⟩

theorem under_cPl (w : Pl D.host.E) : (cPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show cj _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ w.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ w.asIdeal
  rw [cj_algMap D.sp.cm]

theorem eq_or_of_under_eq {w w' : Pl D.host.E} (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F)) :
    w = w' ∨ w = cPl w' := by
  have hsub : (w.asIdeal : Set (𝓞 D.host.E)) ⊆ w'.asIdeal ∪ (cPl w').asIdeal := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_norm D.sp.cm y
    have h1 : x ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ w.asIdeal
      rw [hx]; exact Ideal.mul_mem_right _ _ hy
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ w'.asIdeal := h1
    rw [hx] at h2
    exact w'.isPrime.mem_or_mem h2
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1))
  · exact Or.inr (HeightOneSpectrum.ext (w.isMaximal.eq_of_le (cPl w').isPrime.ne_top h1))

theorem below_bijective (k : Fin 2) : Function.Bijective (below (D := D) k) := by
  constructor
  · intro v v' e
    rcases eq_or_of_under_eq (congrArg Subtype.val e) with h | h
    · exact D.naut.plGw_inj k h
    · exact absurd h (plGw_ne_cPl k v v')
  · rintro ⟨u, hu⟩
    have hu1 := u.isPrime
    obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (u.asIdeal.primesOver (𝓞 D.host.E)))
    let w : Pl D.host.E := ⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot u.ne_bot W⟩
    have hwv : w.under (𝓞 D.host.F) = u := HeightOneSpectrum.ext hWv.over.symm
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← hwv] at hu
      have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal := hu
      rwa [map_natCast] at h1
    obtain ⟨v, h | h⟩ := cover k w hg
    · exact ⟨v, Subtype.ext (show (D.naut.plGw k v).under (𝓞 D.host.F) = u by rw [← h, hwv])⟩
    · exact ⟨v, Subtype.ext (show (D.naut.plGw k v).under (𝓞 D.host.F) = u by rw [← under_cPl, ← h, hwv])⟩

def sqEquiv (D : D7) : (Σ k : Fin 2, D.nd.PlG k) ≃ LevelCuspCharacters.Sq D.host :=
  Equiv.sigmaCongrRight fun k => Equiv.ofBijective _ (below_bijective k)

section Match

variable {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg)


end Match

def pull (x : LevelCuspCharacters.LevelGroup D.host) : G0g D.nd := fun kv => x ⟨kv.1, below kv.1 kv.2⟩

theorem pull_bijective : Function.Bijective (pull (D := D)) :=
  (Equiv.piCongrLeft (fun v : LevelCuspCharacters.Sq D.host => GL (Fin D.R.r) (ZMod (D.host.g v.1))) (sqEquiv D)).symm.bijective

def IdemTie (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Prop :=
  ∀ x, D.ntypes.e0.coeff (pull x) = (LevelCuspCharacters.goodIdem (H := D.host) om).coeff x

section Idem

variable {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg) {b : Pg ≃ LevelCuspCharacters.Sq D.host} (hb : BadPlacesGoodCoefficients.IsBelow b)
  (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1)

end Idem

section Parts

variable {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg) (θ : LinearCoefficientData.InfFam D) (P : LevelP Pg D.R.r ℂ)
  (c : LinearCoefficientData.Eig D)

end Parts

section Level

variable {Pg : Finset (Pl D.host.E)}

def FirstAtBad (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∀ (θ : LinearCoefficientData.InfFam D), IsInfFam θ →
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (M₁ : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (β₁ : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    BadPlacesGoodCoefficients.IsFrameAtG (D.sp.Y 0) β₀ → BadPlacesGoodCoefficients.IsFrameAtG (D.sp.W j) β₁ →
  ∀ c : LinearCoefficientData.Eig D,
    FiniteDimensional ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P (BadPlacesGoodCoefficients.badPlaces D) c) ∧
      FiniteDimensional ℂ (LinearCoefficientData.Wc θ j h1 h2 M₁ h β₁ P (BadPlacesGoodCoefficients.badPlaces D) c) ∧
      Module.finrank ℂ (LinearCoefficientData.Wc θ j h1 h2 M₁ h β₁ P (BadPlacesGoodCoefficients.badPlaces D) c) =
        Module.finrank ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P (BadPlacesGoodCoefficients.badPlaces D) c)

variable (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ)

end Level

def FirstRec (D : D7) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)) (h : LinearCoefficientData.IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
    IsGenericPsi Pg ψ → FirstAtBad h (P0 Pg D.R.r ψ)

section Above

variable {Pg : Finset (Pl D.host.E)}

theorem eq_cPl_of_isConjPl {w w' : Pl D.host.E} (h : Lev.IsConjPl w w') : w = cPl w' := by
  refine HeightOneSpectrum.ext (w.isMaximal.eq_of_le (cPl w').isPrime.ne_top fun c hc => ?_)
  obtain ⟨c', hc', e⟩ := h c hc
  have : c' = cj _ c := RingOfIntegers.ext e
  rwa [mem_cPl, ← this]

end Above

def TameTie (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Prop :=
  ∀ k : Fin 2, ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
    (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
    ∀ v j, ∃ χ, (χ = LevelCuspCharacters.chiTame (H := D.host) om k j ∨ χ = (LevelCuspCharacters.chiTame (H := D.host) om k j)⁻¹) ∧
      ∀ a : (ZMod (D.host.g k))ˣ,
        GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod (D.host.g k)) _ (D.nd.chiT k v j : ZMod (D.host.g k)))
          (algebraMap (ZMod (D.host.g k)) _ (a : ZMod (D.host.g k))) = ((χ a : ℂˣ) : ℂ)

theorem TameTie.eSerTie {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (h : TameTie D om) : GlobalTheory.GLq.ESerTie D :=
  fun k => let ⟨L, h1, h2, _⟩ := h k; ⟨L, h1, h2⟩

section Comparison₂

open GlobalTheory.ParamLabel GlobalTheory.GLq

theorem irr_one_ne_zero {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsIrr χ) : χ 1 ≠ 0 := by
  intro h0
  have h1 := (_root_.GlobalTheory.GLq.ZOrth.zorth G χ χ h h).2.2
  obtain ⟨V, -, hV⟩ := h
  have h2 : Module.finrank ℂ V = 0 := by
    have := hV 1
    rw [FDRep.char_one, h0] at this
    exact_mod_cast this
  haveI : Subsingleton V := Module.finrank_zero_iff.1 h2
  have h3 : ∀ x, χ x = 0 := fun x => by
    rw [← hV, FDRep.character, Subsingleton.elim (V.ρ x) 0, map_zero]
  simp [ip, h3] at h1

theorem eq_of_prod_eq {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    {χ χ' : ∀ i, G i → ℂ} (h : ∀ i, IsIrr (χ i)) (h' : ∀ i, IsIrr (χ' i))
    (e : ∀ a : ∀ i, G i, ∏ i, χ i (a i) = ∏ i, χ' i (a i)) (i : ι) : χ i = χ' i := by
  classical
  have key : ∀ (χ : ∀ i, G i → ℂ) (y : G i), ∏ k, χ k (Pi.mulSingle (M := G) i y k) = χ i y * ∏ k ∈ Finset.univ.erase i, χ k 1 := by
    intro χ y
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Pi.mulSingle_eq_same]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hk)]
  by_contra hne
  have h1 := (_root_.GlobalTheory.GLq.ZOrth.zorth _ _ _ (h i) (h i)).2.2
  have h2 := (_root_.GlobalTheory.GLq.ZOrth.zorth _ _ _ (h i) (h' i)).2.2
  rw [if_pos rfl] at h1
  rw [if_neg hne] at h2
  have h3 : ip (χ i) (χ i) * ∏ k ∈ Finset.univ.erase i, χ k 1 = ip (χ i) (χ' i) * ∏ k ∈ Finset.univ.erase i, χ' k 1 := by
    simp only [ip, mul_assoc, Finset.sum_mul, ← key, e]
  rw [h1, h2, one_mul, zero_mul] at h3
  exact Finset.prod_ne_zero_iff.2 (fun k _ => irr_one_ne_zero (h k)) h3

def Rel (L : ∀ k, LabelDatum (D.host.g k)) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1))
    (s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r) : Prop :=
  ∀ k v, ∃ x, Labels (L k) (s ⟨k, below k v⟩) x (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))

theorem TameTie.idemTie (hG : Green) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hT : TameTie D om) : IdemTie D om := by
  classical
  choose L _ hE hχ using hT
  have h5 := five_le_typePrime D
  have good : ∀ a s, Rel L a s →
      (D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔ LevelCuspCharacters.IsGoodParam om s) := by
    intro a s h
    refine forall_congr' fun k => ?_
    choose x hx using h k
    rw [← goodAt_comp _ (below k) (below_bijective k).2]
    refine (good_iff (L k) (h5 k) _ x _ hx _ (D.nd.chiT k) fun v j => ?_).symm
    obtain ⟨χ, rfl | rfl, h⟩ := hχ k v j
    exacts [Or.inl h, Or.inr h]
  have ser : ∀ a s, Rel L a s → D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) → ∀ k v,
      {χ | IsIrr χ ∧ HasLabel (L k) χ (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))} = {LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)} ∧
      eSerC (L k) D.R.r (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) = LevelCuspCharacters.centralIdem (LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)) := by
    intro a s h hg k v
    obtain ⟨x, hx⟩ := h k v
    exact hx.series hG (h5 k) ((hg k).1.2.1 v)
  have mem : ∀ a s, Rel L a s → D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) → ∀ k v,
      IsIrr (LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)) ∧
        HasLabel (L k) (LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)) (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := fun a s h hg k v =>
    ((Set.ext_iff.1 (ser a s h hg k v).1) _).2 rfl
  have exa : ∀ s, ∃ a, Rel L a s := by
    intro s
    choose x f hf using fun kv : (Σ k : Fin 2, D.nd.PlG k) => _root_.GlobalTheory.ParamLabel.exists_labels _ (L kv.1) _ (s ⟨kv.1, below kv.1 kv.2⟩)
    refine ⟨fun kv i => (f kv).coeff i, fun k v => ⟨x ⟨k, v⟩, ?_⟩⟩
    rw [Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (hf ⟨k, v⟩).2.2.1 (_root_.GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor _ _ _ _ _ (hf ⟨k, v⟩).2).1]
    exact hf ⟨k, v⟩
  have exs : ∀ a, D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) → ∃ s, Rel L a s := by
    intro a hg
    choose s hs using fun k v => _root_.GlobalTheory.ParamExists.param_exists _ (L k) _ _ ((hg k).1.1 v).1 ((hg k).1.1 v).2.1 ((hg k).1.1 v).2.2 ((hg k).1.2.1 v)
    refine ⟨fun w => s w.1 ((Equiv.ofBijective _ (below_bijective w.1)).symm w.2), fun k v => ?_⟩
    have : (Equiv.ofBijective _ (below_bijective k)).symm (below k v) = v :=
      (Equiv.ofBijective _ (below_bijective k)).symm_apply_apply v
    have e : ∀ v', v' = v → ∃ x, Labels (L k) (s k v') x (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := fun v' e => e ▸ hs k v
    exact e _ this
  choose S hS using exs
  have tup : ∀ s y, LevelCuspCharacters.tupleChar (H := D.host) (K := ℂ) s y =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), LevelCuspCharacters.typeChar (s ⟨kv.1, below kv.1 kv.2⟩) (pull y kv) := fun s y => by
    letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
    exact (Fintype.prod_equiv (sqEquiv D) _ _ fun kv => rfl).symm
  intro y
  show (∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (pull y kv) else 0) = _
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  simp only [LevelCuspCharacters.goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_bij (fun a ha => LevelCuspCharacters.tupleChar (S a (Finset.mem_filter.1 ha).2)) (fun a ha => ?_)
    (fun a ha a' ha' e => ?_) (fun τ hτ => ?_) (fun a ha => ?_)
  · exact (Set.Finite.mem_toFinset _).2 ⟨_, (good a _ (hS a _)).1 (Finset.mem_filter.1 ha).2, rfl⟩
  · have m := mem a _ (hS a (Finset.mem_filter.1 ha).2) (Finset.mem_filter.1 ha).2
    have m' := mem a' _ (hS a' (Finset.mem_filter.1 ha').2) (Finset.mem_filter.1 ha').2
    funext kv
    have e1 := eq_of_prod_eq (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (m kv.1 kv.2).1) (fun kv => (m' kv.1 kv.2).1)
      (fun z => by
        obtain ⟨y, rfl⟩ := pull_bijective.2 z
        rw [← tup, ← tup, e]) kv
    have e2 := Label.label_unique (L kv.1) (h5 _) _ (m kv.1 kv.2).1 _ _ (m kv.1 kv.2).2 (e1 ▸ (m' kv.1 kv.2).2)
    funext i
    rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (a kv) i, ← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (a' kv) i]
    exact congrArg (fun p => p.coeff i) e2
  · obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
    obtain ⟨a, ha⟩ := exa s
    have hg := (good a s ha).2 hs
    refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩, funext fun z => ?_⟩
    rw [tup, tup]
    refine Finset.prod_congr rfl fun kv _ => congrFun (Set.singleton_injective ?_) _
    rw [← (ser a _ (hS a hg) hg kv.1 kv.2).1, ← (ser a _ ha hg kv.1 kv.2).1]
  · have hg := (Finset.mem_filter.1 ha).2
    have hc : (Nat.card (LevelCuspCharacters.LevelGroup D.host) : ℂ) =
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (Nat.card (Gn (D.host.g kv.1) D.R.r) : ℂ) := by
      rw [Nat.card_eq_of_bijective _ pull_bijective, Nat.card_pi, Nat.cast_prod]
    rw [coeff_centralIdem, tup, tup, hc, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [hE, (ser a _ (hS a hg) hg kv.1 kv.2).2, coeff_centralIdem]
    rfl

end Comparison₂

section Move

open Formalism.IndefR.Lev Formalism.L2.DIV

variable {Pg Pg' : Finset (Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1))
  (φ₁ : ∀ PP : ↥Pg, ZMod (D.host.g (pl.symm PP).1) ≃+* kP PP.1) (b : ↥Pg' ≃ LevelCuspCharacters.Sq D.host)
  (φ : ∀ PP : ↥Pg', ZMod (D.host.g (b PP).1) ≃+* kP PP.1) (S : Set (LevelCuspCharacters.Sq D.host))

end Move

theorem tameTie_of_typesTrue {P : Formalism.L2.Host.PiBar D.host} {W : Formalism.L2.Host.Omg D.host}
    (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes P W) :
    LevelCuspCharacters.IsGeneratorFamily (H := D.host) W.om ∧ TameTie D W.om ∧ OnePrime D :=
  ⟨W.gen, fun k => ⟨_, (h.teich k).symm, h.ser k, fun v j =>
    ⟨_, Or.inl rfl, fun a => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab _ (h.isCharLab k v j) a⟩⟩,
    fun k v v' => (h.pl k v).trans (h.pl k v').symm⟩

def Tied (D : D7) : Prop :=
  (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) ∧ ∃ om, LevelCuspCharacters.IsGeneratorFamily (H := D.host) om ∧ TameTie D om

def Core : Prop := ∀ D : D7, Tied D → FirstRec D

end GlobalTheory.DimPartsCompare

end
