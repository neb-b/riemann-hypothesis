module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesGoodAlmostAllPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqNcardPrimesOver
section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.SplitResidue

theorem card_eq_ncard_primesOver (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // (g : 𝓞 E) ∈ w.asIdeal} =
      (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)
  · haveI := w.1.isPrime
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using w.2
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro ⟨P, hP, hPl⟩
    refine ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1
      (Ideal.mem_span_singleton_self _)

theorem residue_and_unramified : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely E g →
    ∀ w : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ w.asIdeal →
      Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod g) ∧ (g : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro E _ _ g hg h w hw
  haveI := w.isPrime
  haveI := Fact.mk hg
  have h' := (card_eq_ncard_primesOver E hg).symm.trans h
  obtain ⟨h1, h2⟩ := GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw
  refine ⟨?_, h1⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  refine ⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal))
    ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := h2 x
  refine ⟨(m : ZMod g), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]
  exact hm

end GlobalTheory.SplitResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace

theorem term_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (ha : S.a = 0)
    {d d₁ : S.Datum} {Λ Λ₁ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (hT₁ : S.IsTerm d₁ Λ₁)
    (hM : S.M d Λ = S.M d₁ Λ₁) : ∃ h ∈ S.H0, h • Λ₁ = Λ := by
  have : IsArtinianRing E := by
    have := L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
    exact IsArtinianRing.of_finite F E
  obtain ⟨u₀, hu₀, hE, hui, hup⟩ := _root_.GlobalTheory.HL.FrameUnimod.frame_unimodular L r k S d Λ hT ha
  obtain ⟨b₀, hbW, hΛ, hbi, hbp⟩ := _root_.GlobalTheory.HL.UnimodSplit.main L r k S d Λ hT ha
  obtain ⟨c₀, hcW, hΛ₁, hci, hcp⟩ := _root_.GlobalTheory.HL.UnimodSplit.main L r k S d₁ Λ₁ hT₁ ha
  obtain ⟨u, huo, hus⟩ := _root_.GlobalTheory.HL.SelfDual.exists_orthonormal_same_span L S.Hm S.herm u₀ hui hup
  obtain ⟨b, hbo, hbs⟩ := _root_.GlobalTheory.HL.SelfDual.exists_orthonormal_same_span L S.Hm S.herm b₀ hbi hbp
  obtain ⟨c, hco, hcs⟩ := _root_.GlobalTheory.HL.SelfDual.exists_orthonormal_same_span L S.Hm S.herm c₀ hci hcp
  have hsp : ∀ (w : Fin (k - 1) → S.V) (w₀ : Fin (k - 1) → S.V), (∀ i, w₀ i ∈ S.W0) →
      Submodule.span L.O (Set.range w) = Submodule.span L.O (Set.range w₀) → ∀ i, w i ∈ S.W0 := by
    intro w w₀ h0 he i
    have h1 : w i ∈ Submodule.span L.O (Set.range w₀) := by
      rw [← he]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range w₀) ≤ S.W0.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    exact h2 h1
  have hbW' := hsp b b₀ hbW hbs
  have hcW' := hsp c c₀ hcW hcs
  have huME : ∀ i, u i ∈ S.ME := by
    intro i
    have h1 : u i ∈ Submodule.span L.O (Set.range u₀) := by
      rw [← hus]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range u₀) ≤ S.ME.restrictScalars L.O :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        rw [← hE]; exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 h1
  have horth : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm w (u i) = 0 := fun hw i => hw _ (huME i)
  have horth' : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm (u i) w = 0 := fun hw i => by
    rw [GlobalTheory.FrameBasic.hf_conj L S.herm.1, horth hw i, map_zero]

  let x : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u c
  let y : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u b
  have gx : ∀ i j, hf L S.Hm (x i) (x j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [x, huo, Fin.ext_iff]
    · simp [x, horth' (hcW' j), Fin.ext_iff]; omega
    · simp [x, horth (hcW' i), Fin.ext_iff]; omega
    · simp [x, hco, Fin.ext_iff]
  have gy : ∀ i j, hf L S.Hm (y i) (y j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [y, huo, Fin.ext_iff]
    · simp [y, horth' (hbW' j), Fin.ext_iff]; omega
    · simp [y, horth (hbW' i), Fin.ext_iff]; omega
    · simp [y, hbo, Fin.ext_iff]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.HermTuple.witt_tuples L S.Hm S.herm _ x y
    (fun i j => by rw [gx, gy]) (by
      have : (Matrix.of fun i j => hf L S.Hm (x i) (x j)) = 1 := by
        ext i j; simp [gx, Matrix.one_apply]
      rw [this]; simp)
  have hgu : ∀ i, g (u i) = u i := fun i => by
    have := hgx (Fin.castAdd _ i)
    simpa [x, y] using this
  have hgc : ∀ i, g (c i) = b i := fun i => by
    have := hgx (Fin.natAdd _ i)
    simpa [x, y] using this
  have hfix : ∀ v ∈ S.ME, g v = v := by
    intro v hv
    rw [← hE] at hv
    let K : Submodule E S.V := LinearMap.eqLocus (g : S.V →ₗ[E] S.V) LinearMap.id
    have h1 : Submodule.span L.O (Set.range u) ≤ K.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hgu i)
    have h2 : Submodule.span E (Set.range u₀) ≤ K :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        apply h1
        rw [hus]
        exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 hv
  have hH0 : g ∈ S.H0 :=
    ⟨hg, GlobalTheory.HL.FrameStab.mem_unipOn' bot_le g fun v hv => by rw [hfix v hv, sub_self]; exact Submodule.zero_mem _⟩
  have hsm : ∀ s : Set S.V, g • Submodule.span L.O s = Submodule.span L.O (g '' s) := fun s => by
    rw [Submodule.pointwise_smul_def, Submodule.map_span]; rfl
  have e1 : g • S.M d Λ = S.M d Λ := by
    rw [hu₀, ← hus, hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgu i
  have e2 : g • Submodule.span L.O (Set.range c) = Submodule.span L.O (Set.range b) := by
    rw [hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgc i
  refine ⟨g, hH0, ?_⟩
  have e3 : ∀ A B : Submodule L.O S.V, g • (A ⊔ B) = g • A ⊔ g • B := fun A B => by
    simp only [Submodule.pointwise_smul_def, Submodule.map_sup]
  rw [hΛ₁, ← hM, ← hcs, e3, e1, e2, hbs, ← hΛ]

theorem good_place {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k) (hG : Good S) :
    S.Hp = 1 ∧ S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 ∧ ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 ∧
      S.om d₀ (coordLat S) = 1 ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d₀ = S.complementReferenceCompactSubgroup ∧
      (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • coordLat S) ∧
      (∀ Λ, S.IsTerm d₀ Λ → S.Fr d₀ Λ = S.frameCls S.f S.f' → Λ = coordLat S) ∧
      ∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀ := by
  obtain ⟨hvG, hvD⟩ := _root_.GlobalTheory.HL.StdPlace.vE_G_D_eq_zero L r k S hG
  have hvth : S.vth = 0 := by simp [Frames.vth, hG.gg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hvG]
  obtain ⟨d₀, hd₀⟩ := _root_.GlobalTheory.HL.CoordGood.main L r k S hG
  have hT₀ : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hd₀⟩
  obtain ⟨hom, hM₀, hFr₀, -, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ _ _ _ hd₀
  have hFr₁ : S.Fr d₀ (coordLat S) = S.frameCls S.f S.f' := hFr₀
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hG.gg hG.D_unit
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  refine ⟨(GlobalTheory.HL.GoodPlace.equality L r k S hk hG.gg hvG hvD).2.1, _root_.GlobalTheory.HL.StdStab.stab_coordLat L r k S hG ha d₀ hd₀, d₀, hd₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hom]
    have h1 : ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V),
        (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → S.psiOf g gs 1 = 1 := by
      intro g gs hd
      have : ∀ j, S.coef g gs 1 j = 0 := fun j => by
        have := hd j.succ j
        rw [if_neg (by simp [Fin.ext_iff])] at this
        exact this
      simp [Frames.psiOf, this]
    have e1 : S.psi 1 = 1 := h1 _ _ S.dual
    have e2 : S.psi' 1 = 1 := h1 _ _ S.dual'
    simp [e1, e2]
  · ext h
    simp only [Subgroup.mem_inf, Frames.complementReferenceCompactSubgroup, MulAction.mem_stabilizer_iff]
    refine and_congr_right fun hh => ⟨fun e => ?_, fun e => ?_⟩
    · have h1 := hcom d₀ _ hT₀ h hh
      rw [e] at h1
      have := (huniq d₀ _ hT₀).2 _ h1.1 h1.2.2.2.2.2
      exact this
    · have h1 := hcom d₀ _ hT₀ h hh
      have e' : h • coordLat S = coordLat S := e
      rw [e'] at h1
      exact hdd _ _ _ hT₀ h1.1
  · intro Λ hΛ
    obtain ⟨h, hh, e⟩ := hall _ (hint _ _ hΛ)
    refine ⟨h, hh, ?_⟩
    have h2 := hact d₀ _ hT₀ h hh
    exact (huniq d₀ _ h2.1).2 _ hΛ (by rw [h2.2.2.2.2.1, hFr₁, e])
  · intro Λ hΛ e
    exact (huniq d₀ _ hT₀).2 _ hΛ (by rw [e, hFr₁])
  · intro d Λ hΛ
    obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hΛ)
    have hsi := S.St.inv_mem hs
    have h2 := hact d _ hΛ _ hsi
    have hT₂ := h2.1
    have hFr₂ : S.Fr d (s⁻¹ • Λ) = S.Fr d₀ (coordLat S) := by
      rw [h2.2.2.2.2.1, e, hFr₁, smul_smul, inv_mul_cancel, one_smul]
    have hM₂ : S.M d (s⁻¹ • Λ) = S.M d₀ (coordLat S) := by
      have h3 : (S.fr d (s⁻¹ • Λ), S.fr' d (s⁻¹ • Λ)) ∈ S.Fr d₀ (coordLat S) := by
        rw [← hFr₂]; exact (hcls _ _).1
      exact ((hcls _ _).2.1 _ h3).2
    obtain ⟨h, hh, e₁⟩ := term_orbit L r k S ha hT₂ hT₀ hM₂
    refine ⟨h, hh, ?_⟩
    have h4 := (hcom d₀ _ hT₀ h hh).1
    rw [e₁] at h4
    exact hdd _ _ _ h4 hT₂

theorem coordinate_lattice_standard : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → {p | ¬ ((G.S p).gg = false ∧ (G.S p).Hp = 1 ∧ (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = (G.S p).K0 ∧ ∃ d₀, (G.S p).IsTermW d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) 1 1 ∧ (G.S p).om d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = 1 ∧ (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV d₀ = (G.S p).complementReferenceCompactSubgroup ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → ∃ h ∈ (G.S p).St, Λ = h • (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → (G.S p).Fr d₀ Λ = (G.S p).frameCls (G.S p).f (G.S p).f' → Λ = (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ ∀ d Λ, (G.S p).IsTerm d Λ → ∃ h ∈ (G.S p).H0, d = h • d₀)}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk
  refine (_root_.GlobalTheory.HL.StdPlace.good_almost_all A r k G).subset fun p hp hg => hp ?_
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  exact ⟨hg.gg, good_place (A.L p) r k (G.S p) hk hg⟩

end GlobalTheory.HL.StdPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormal
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.MaxExists

open NumberField Matrix in
open scoped ENNReal Classical in
private lemma isIntLat_of_isUnimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K M)
    (hU : _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M) : _root_.GlobalTheory.Mass.IsIntLat h M := by
  unfold _root_.GlobalTheory.Mass.IsIntLat
  refine ⟨hL, ?_⟩
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  intro x hx y hy
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular at hU
  have hy' : y ∈ _root_.Formalism.HermitianLatticesTheory.dual h M := by rw [hU]; exact hy
  exact (_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M y).1 hy' x hx

open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.MaxExists.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M → ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M → _root_.GlobalTheory.Mass.IsMaxLat h M ∧ _root_.GlobalTheory.Mass.badP h M = ∅ ∧ _root_.GlobalTheory.Mass.lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h M n → Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M ∧ Module.finrank K V = n) := by
  intro K V _ _ _ _ _ _ _ _ h hK hS hN
  have D := fun M hM => _root_.GlobalTheory.Mass.DiscOrder.main K V h hK hS hN M hM
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ n : ℕ, ∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M →
        _root_.GlobalTheory.Mass.discN h M = n →
        ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M' := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hM hn
        by_cases hmax : ∀ N : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h N → M ≤ N → N = M
        · exact ⟨M, by unfold _root_.GlobalTheory.Mass.IsMaxLat; exact ⟨hM, hmax⟩, le_rfl⟩
        · push_neg at hmax
          obtain ⟨N, hNi, hMN, hne⟩ := hmax
          obtain ⟨hidx0, hdisc⟩ := (D M hM).2.2.1 N hNi hMN
          have hidx1 : _root_.GlobalTheory.Mass.idxN N M ≠ 1 := by
            intro h1
            exact hne (le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1) hMN)
          have hNpos : 0 < _root_.GlobalTheory.Mass.discN h N :=
            Nat.pos_of_ne_zero (D N hNi).1
          have hlt : _root_.GlobalTheory.Mass.discN h N < n := by
            rw [← hn, hdisc]
            have h2 : 2 ≤ _root_.GlobalTheory.Mass.idxN N M := by omega
            have h4 : 1 < _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
              Nat.one_lt_pow (by norm_num) (by omega)
            calc _root_.GlobalTheory.Mass.discN h N
                = _root_.GlobalTheory.Mass.discN h N * 1 := (mul_one _).symm
              _ < _root_.GlobalTheory.Mass.discN h N * _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
                  Nat.mul_lt_mul_of_pos_left h4 hNpos
          obtain ⟨M', hM', hNM'⟩ := ih _ hlt N hNi rfl
          exact ⟨M', hM', hMN.trans hNM'⟩
    exact fun M hM => key _ M hM rfl
  · intro M hL hU
    have hI := isIntLat_of_isUnimodular hL hU
    have hD1 : _root_.GlobalTheory.Mass.discN h M = 1 := ((D M hI).2.1).2 hU
    have hbad : _root_.GlobalTheory.Mass.badP h M = ∅ := by
      unfold _root_.GlobalTheory.Mass.badP
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hP
      refine (D M hI).2.2.2.2.1 P hP ?_
      rw [hD1, Nat.cast_one]
      exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
    refine ⟨?_, hbad, ?_⟩
    · unfold _root_.GlobalTheory.Mass.IsMaxLat
      refine ⟨hI, fun N hNi hMN => ?_⟩
      obtain ⟨_, hdisc⟩ := (D M hI).2.2.1 N hNi hMN
      rw [hD1] at hdisc
      have h1 : _root_.GlobalTheory.Mass.idxN N M ^ 2 = 1 :=
        Nat.eq_one_of_mul_eq_one_left hdisc.symm
      have h1' : _root_.GlobalTheory.Mass.idxN N M = 1 := by
        simpa using h1
      exact le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1') hMN
    · unfold _root_.GlobalTheory.Mass.lamMax
      rw [hbad]
      exact finprod_mem_empty
  · intro M n hO
    exact ⟨_root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.isUnimodular_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.finrank_of_ortho hO⟩

end GlobalTheory.Mass.MaxExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameClasses_total_weight_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∃ d Λ, S.IsTerm d Λ) → (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  first | exact @GlobalTheory.HL.TotalWeight.sumCls_one_le | exact GlobalTheory.HL.TotalWeight.sumCls_one_le | (intros; apply GlobalTheory.HL.TotalWeight.sumCls_one_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbitsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) ∧ LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧ (∑' t : R.RT d, ENNReal.ofReal (LocNG.mu P t.1)) = S.mass (c.dat d) (fun _ => True) := by
  first | exact @GlobalTheory.HL.CoordAmp.amp_mass_eq | exact GlobalTheory.HL.CoordAmp.amp_mass_eq | (intros; apply GlobalTheory.HL.CoordAmp.amp_mass_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesDefectOrderShareLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectShare

lemma tsum_subtype_le {α : Type} (P : α → Prop) (s : Set α) (hs : ∀ a, P a → a ∈ s) (f : α → ℝ≥0∞)
    (c N : ℝ≥0∞) (hf : ∀ a, P a → f a ≤ c) (hN : (s.encard : ℝ≥0∞) ≤ N) :
    ∑' a : {a // P a}, f a ≤ N * c := by
  calc ∑' a : {a // P a}, f a ≤ ∑' _ : ({a | P a} : Set α), c :=
        ENNReal.tsum_le_tsum fun a => hf a.1 a.2
    _ = (({a | P a} : Set α).encard : ℝ≥0∞) * c := ENNReal.tsum_set_const _ _
    _ ≤ N * c := by
        gcongr
        refine le_trans ?_ hN
        exact_mod_cast Set.encard_le_encard (fun a ha => hs a ha)

theorem share_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (C : Set S.FrP) (hC : S.IsCls C) (β : ℕ) (_hβ : 1 ≤ β) :
    (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤
      ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) *
        S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  by_cases h : ∃ d Λ, S.IsTerm d Λ ∧ S.Fr d Λ = C
  swap
  · have h0 : (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) = 0 := by
      unfold Frames.sumData
      refine ENNReal.tsum_eq_zero.2 fun o => ?_
      have : ({Λ | S.IsTerm o.out Λ ∧ S.be o.out Λ = β ∧ S.Fr o.out Λ = C} :
          Set (Submodule L.O S.V)) = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, h3⟩
        exact h ⟨_, _, h1, h3⟩
      simp [Frames.nT, this]
    rw [h0]
    exact zero_le
  obtain ⟨d, Λ, hT, hFr⟩ := h
  obtain ⟨hSD, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have ha : 0 ≤ S.a := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).1
  have hp : (S.fr d Λ, S.fr' d Λ) ∈ C := by
    rw [← hFr]
    exact (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
  obtain ⟨κ, hκ, hU⟩ := _root_.GlobalTheory.HL.FrameMass.mass_trace L r k S (by omega) ⟨Λ, hSD⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HL.ClassMass.class_mass L r k S C hC _ hp
  have h3 := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC _ hp ha
  have hlow : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.Mof (S.fr d Λ) (S.fr' d Λ)) := by
    have := (hU C hC _ hp _ le_rfl (fun x hx => (hM hx).2)
      (fun x hx y hy => (hSD.2 y).2 (hM hy).1 x (hM hx).1)).1
    simpa using this
  rw [h2]
  refine (h1 fun n => n = β).trans ?_
  refine (tsum_subtype_le _ _ (fun Mh hMh => ?_) S.massSig
    (ENNReal.ofReal (2 * κ * ((β : ℝ) ^ (k - 1))⁻¹)) _ (fun Mh hMh => ?_) h3).trans ?_
  · exact ⟨hMh.1, hMh.2.1, hMh.2.2.1⟩
  · have := (hU C hC _ hp Mh hMh.1 hMh.2.1 hMh.2.2.1).2
    rw [hMh.2.2.2] at this
    exact this
  · refine le_trans (le_of_eq ?_) (mul_le_mul_right hlow _)
    have hz : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = (S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2)) := by
      rw [← zpow_natCast]
      congr 1
      push_cast
      rw [Int.toNat_of_nonneg ha]
    have hq : (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) =
        ENNReal.ofReal ((S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    rw [hz, hq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end GlobalTheory.HL.DefectShare
end

