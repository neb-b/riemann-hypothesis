module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PointEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ThickOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FirstPrimeConditionTransfer
section
theorem UpperTheory.V.Pr.p1Of :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.FirstPrimeConditionTransfer := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ h4 J hJ x L p hp hTI hM P hP hPp
  have key : ∀ Q : Ideal L.R, J.map Φ ≤ L.π Q ↔ J ≤ Q.comap (T.phi Φ L : T.B.B →+* L.R) := by
    intro Q
    rw [Ideal.map_le_iff_le_comap]
    exact Iff.rfl
  obtain ⟨y, j, hker, hloc, hρ, hψ, hpt⟩ :=
    UpperTheory.V.Pr.pointEx l O F n T Φ hΦ x L p hp.prime hp.dim hp.char
  subst hker
  obtain ⟨h1, h3, hI, -⟩ := UpperTheory.V.Pr.niceOf l O F n T x L y j hloc hp hρ hψ
  rw [key] at hM ⊢
  haveI := hP
  exact hJ y (j.comp (T.phi Φ L)) ⟨h1, hI hTI, h3, h4 y⟩ hpt (fun a ha => hM ha) (T.back Φ L P)
    (fun a ha => hPp ha)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NotIrrOfChar
section
open Matrix Polynomial UpperTheory.V.U3 Formalism.MainNotions.N

private noncomputable def diagRep {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) :
    G →* GL (Fin n) κ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin n => κ)).symm.toMonoidHom.comp (MonoidHom.pi χ))

private theorem diagRep_val {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) (g : G) :
    (diagRep χ g : Matrix (Fin n) (Fin n) κ) = diagonal fun i => ((χ i g : κˣ) : κ) := rfl

private theorem diagRep_single {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) (g : G)
    (i : Fin n) : (diagRep χ g : Matrix (Fin n) (Fin n) κ) *ᵥ Pi.single i 1 =
      ((χ i g : κˣ) : κ) • (Pi.single i 1 : Fin n → κ) := by
  ext j
  rw [diagRep_val, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

private theorem diagRep_span {G κ ι : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) (a : ι → Fin n) :
    IsInv (diagRep χ) (Submodule.span κ (Set.range fun i => (Pi.single (a i) 1 : Fin n → κ))) := by
  intro g v hv
  have hle : Submodule.span κ (Set.range fun i => (Pi.single (a i) 1 : Fin n → κ)) ≤
      (Submodule.span κ (Set.range fun i => (Pi.single (a i) 1 : Fin n → κ))).comap
        (Matrix.mulVecLin (diagRep χ g : Matrix (Fin n) (Fin n) κ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, diagRep_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hle hv

private theorem diagRep_ss {G κ : Type} [Group G] [Field κ] {n : ℕ} (χ : Fin n → G →* κˣ) :
    IsSSRep (diagRep χ) := by
  classical
  intro W hW
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun I : Finset (Fin n) => Disjoint W
        (Submodule.span κ ((fun i => (Pi.single i 1 : Fin n → κ)) '' (I : Set (Fin n))))))
      Finset.card ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩⟩
  rw [Finset.mem_filter] at hI
  refine ⟨Submodule.span κ ((fun i => (Pi.single i 1 : Fin n → κ)) '' (I : Set (Fin n))), ?_, hI.2, ?_⟩
  · rw [Set.image_eq_range]
    exact diagRep_span χ (fun i : (I : Set (Fin n)) => (i : Fin n))
  · rw [codisjoint_iff, eq_top_iff, ← (Pi.basisFun κ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    by_contra hj
    have hne : (Pi.single j 1 : Fin n → κ) ≠ 0 := by simp
    have hjI : j ∉ I := fun h => hj (Submodule.mem_sup_right (Submodule.subset_span ⟨j, h, rfl⟩))
    have hd : Disjoint W (Submodule.span κ ((fun i => (Pi.single i 1 : Fin n → κ)) ''
        ((insert j I : Finset (Fin n)) : Set (Fin n)))) := by
      rw [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, sup_comm]
      exact hI.2.disjoint_sup_right_of_disjoint_sup_left ((Submodule.disjoint_span_singleton' hne).2 hj)
    have hc := hmax (insert j I) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩)
    rw [Finset.card_insert_of_notMem hjI] at hc
    omega

theorem UpperTheory.V.Pr.notIrrOfChar :
    UpperTheory.V.Pr.NotIrrOfChar := by
  intro G κ _ _ n hn r χ hch hirr
  have ssr : IsSSRep r := by
    intro W hW
    rcases hirr W (fun g _ v hv => hW g v hv) with rfl | rfl
    · exact ⟨⊤, fun g v _ => Submodule.mem_top, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot κ).1 hv, mulVec_zero]
      exact Submodule.zero_mem _
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (diagRep χ) r (diagRep_ss χ) ssr
    (fun g => by rw [diagRep_val, charpoly_diagonal]; exact (hch g).symm)
  have hn0 : 0 < n := by omega
  set e0 : Fin n → κ := Pi.single (⟨0, hn0⟩ : Fin n) 1 with he0
  set v : Fin n → κ := ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *ᵥ e0 with hv
  have hvne : v ≠ 0 := by
    intro h0
    have hPv : ((P : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *ᵥ v = e0 := by
      rw [hv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [h0, mulVec_zero] at hPv
    have h1 := congrFun hPv ⟨0, hn0⟩
    simp [he0] at h1
  have hinv : ∀ g ∈ (⊤ : Subgroup G), ∀ u ∈ κ ∙ v, UpperTheory.V.Pr.gm r g *ᵥ u ∈ κ ∙ v := by
    intro g _ u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hrg : UpperTheory.V.Pr.gm r g = ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) *
        (diagRep χ g : Matrix (Fin n) (Fin n) κ) * ((P : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) := by
      show ((r g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = _
      rw [hP g, Units.val_mul, Units.val_mul]
    rw [mulVec_smul, hrg, hv, mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul P, mul_inv_cancel,
      Units.val_one, Matrix.mul_one, ← mulVec_mulVec, he0, diagRep_single, mulVec_smul, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rcases hirr (κ ∙ v) hinv with h | h
  · exact hvne ((Submodule.span_singleton_eq_bot).1 h)
  · have hr := finrank_span_singleton (K := κ) hvne
    rw [h, finrank_top, Module.finrank_fin_fun] at hr
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransfer
section
private theorem chain_nat {α : Type} {r : α → α → Prop} {p q : α} (H : Relation.ReflTransGen r p q) :
    ∃ (h : ℕ) (c : ℕ → α), c 0 = p ∧ c h = q ∧ ∀ i < h, r (c i) (c (i + 1)) := by
  induction H with
  | refl => exact ⟨0, fun _ => p, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b d _ hbd ih =>
    obtain ⟨h, c, h0, hh, hs⟩ := ih
    refine ⟨h + 1, fun i => if i ≤ h then c i else d, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hih : i < h
      · have h1 : i ≤ h := le_of_lt hih
        have h2 : i + 1 ≤ h := hih
        simp only [h1, h2, if_true]
        exact hs i hih
      · have hie : i = h := by omega
        subst hie
        simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) from by omega, if_false, hh]
        exact hbd

theorem UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3), T.SecondThirdPrimeConditionTransfer := by
  intro l _ O _ _ _ _ _ F T Φ hΦ hN4 J hJ x L p q hp hTE hch hPex P' hP' hP'q hP'TI
  haveI := L.co
  obtain ⟨P, hP, hPp, hPTI, hJP⟩ := hPex
  obtain ⟨h, c, hc0, hch', hs⟩ := chain_nat hch
  have back_le : ∀ (A : Ideal L.R) [A.IsPrime] (w : UpperTheory.V.W.Point T.r)
      (k : L.R →ₐ[O] w.A), A ≤ RingHom.ker k →
      (T.back Φ L A).asIdeal ≤ RingHom.ker (k.comp (T.phi Φ L)) := by
    intro A _ w k hA z hz
    have h2 : (T.phi Φ L) z ∈ RingHom.ker k := hA hz
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  have hN : ∀ i, i ≤ h → UpperTheory.V.Pr.Nice L.ρ (c i) ∧ L.ρ.TE (c i) := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ⟨(hs i hlt).1, (hs i hlt).2.1⟩
    · rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [hc0]
        exact ⟨hp, hTE⟩
      · have hl := hs (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at hl
        exact ⟨hl.2.2.1, hl.2.2.2.1⟩
  have hpt : ∀ i : Fin (h + 1), ∃ (w : UpperTheory.V.W.Point T.r) (k : L.R →ₐ[O] w.A),
      RingHom.ker k = c i ∧ IsLocalHom k ∧
      UpperTheory.V.W.mat w.ρ = T.K.tw (UpperTheory.V.Fr.NRep.map (↑k) L.ρ) ∧
      w.ψ = T.K.twψ (UpperTheory.V.Fr.NRep.map (↑k) L.ρ) ∧ T.B.IsPt w (k.comp (T.phi Φ L)) := by
    intro i
    have hi := (hN i (Nat.lt_succ_iff.mp i.isLt)).1
    exact UpperTheory.V.Pr.pointEx l O F 3 T Φ hΦ x L (c i) hi.prime hi.dim hi.char
  choose y j hker hloc hmat hψ hIsPt using hpt
  have hNE : ∀ i, (y i).NiceE := by
    intro i
    have hi := hN i (Nat.lt_succ_iff.mp i.isLt)
    have hn : UpperTheory.V.Pr.Nice L.ρ (RingHom.ker (j i)) := by rw [hker]; exact hi.1
    have ht : L.ρ.TE (RingHom.ker (j i)) := by rw [hker]; exact hi.2
    obtain ⟨h1, h3, _, hE⟩ := UpperTheory.V.Pr.niceOf l O F 3 T x L (y i) (j i) (hloc i) hn (hmat i) (hψ i)
    exact ⟨h1, hE ht, h3, hN4 (y i)⟩
  have hlink : ∀ i : Fin h, ∃ E : Ideal L.R, E.IsPrime ∧ UpperTheory.V.Fr.Thick L.ρ E ∧ E ≤ c i ∧ E ≤ c (i + 1) :=
    fun i => (hs i i.isLt).2.2.2.2
  choose E hEp hEt hE1 hE2 using hlink
  let e : Fin h → PrimeSpectrum T.B.B := fun i => @UpperTheory.V.Pr.Setup.back _ _ _ _ _ _ _ _ _ _ T Φ _ L (E i) (hEp i)
  have key := hJ h y (fun i => (j i).comp (T.phi Φ L)) e hNE hIsPt (by
      intro i
      haveI := hEp i
      refine ⟨UpperTheory.V.Pr.thickOf l O F T Φ hΦ x L (E i) (hEt i), ?_, ?_⟩
      · apply back_le
        rw [hker]
        simpa using hE1 i
      · apply back_le
        rw [hker]
        simpa using hE2 i)
    (by
      haveI := hP
      refine ⟨T.back Φ L P, UpperTheory.V.Pr.stableOf l O F 3 T Φ hΦ x L P hPTI, ?_, ?_⟩
      · intro z hz
        exact (Ideal.map_le_iff_le_comap.mp hJP) hz
      · apply back_le
        rw [hker]
        simpa [hc0] using hPp)
  haveI := hP'
  have hfin := key (T.back Φ L P') (by
      apply back_le
      rw [hker]
      simpa [hch'] using hP'q)
    (Or.inl (UpperTheory.V.Pr.stableOf l O F 3 T Φ hΦ x L P' hP'TI))
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  exact hfin hz
end

