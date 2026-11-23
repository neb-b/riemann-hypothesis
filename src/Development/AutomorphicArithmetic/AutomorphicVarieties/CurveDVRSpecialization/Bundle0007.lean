module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesThirdCondition
section
open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

namespace UpperTheory.V.Pr

private lemma open_basis {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ O := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  exact ⟨H.toSubgroup, H.isOpen', hH⟩

private lemma strong_of {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {m : ℕ} (G' V : Subgroup G) (hV : IsOpen (V : Set G))
    (r : G →* GL (Fin m) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r)) :
    StrongIrr (r.comp (V ⊓ G').subtype) := by
  refine strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_
  intro U hU W hW
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ O := by
    have : (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := U.one_mem
    rw [← hOU] at this
    exact this
  obtain ⟨V', hV', hsub⟩ := open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩
  refine hirr V' hV' W fun g hg => ?_
  have h2 := hsub hg.1
  have h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := by
    rw [← hOU]; exact h2.1
  exact hW _ h3

private lemma coset_in {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (U : Set G) (hU : IsOpen U) (s : G) (hs : s ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ h ∈ V, s * h ∈ U := by
  obtain ⟨V, hV, hsub⟩ := open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id))
    (by simpa using hs)
  exact ⟨V, hV, fun h hh => hsub hh⟩

private lemma cosetI {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {n : ℕ} (hn : n ≤ 3) (G' : Subgroup G)
    (r : G →* GL (Fin n) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r))
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin n → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  obtain ⟨h, hh⟩ := regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  simp only [gm, map_mul, Units.val_mul]
  exact hh

private lemma sub_eq {κ : Type} (M : Matrix (Fin 3) (Fin 3) κ) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def cornerHom {G κ : Type} [Group G] [Field κ] (r : G →* GL (Fin 3) κ)
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0) :
    G →* Matrix (Fin 2) (Fin 2) κ where
  toFun g := (gm r g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [sub_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gm]
  map_mul' g h := by
    obtain ⟨a1, a2, a3, a4⟩ := hb g
    obtain ⟨b1, b2, b3, b4⟩ := hb h
    simp only [gm] at a1 a2 a3 a4 b1 b2 b3 b4
    rw [sub_eq, sub_eq, sub_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gm, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, *]

private def midHom {G κ : Type} [Group G] [Field κ] (r : G →* GL (Fin 3) κ)
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0) : G →* κ where
  toFun g := gm r g 1 1
  map_one' := by simp [gm]
  map_mul' g h := by
    obtain ⟨a1, a2, a3, a4⟩ := hb g
    simp only [gm] at a1 a2 a3 a4
    simp [gm, Matrix.mul_apply, Fin.sum_univ_three, *]

private lemma charpoly_block {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ)
    (hb : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0) :
    M.charpoly = (M.submatrix ![0, 2] ![0, 2]).charpoly * (X - C (M 1 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := hb
  rw [sub_eq]
  simp only [Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, *]
  ring

private lemma cosetE {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] (G' : Subgroup G)
    (r : G →* GL (Fin 3) κ) (hc : LinClosed (gm r))
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0)
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') fun g => (gm r g).submatrix ![0, 2] ![0, 2])
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin 3 → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  let σ : G →* GL (Fin 2) κ := (cornerHom r hb).toHomUnits
  let ψ : G →* κˣ := (midHom r hb).toHomUnits
  have hσ : ∀ g, gm σ g = (gm r g).submatrix ![0, 2] ![0, 2] := fun g => rfl
  have hψ : ∀ g, ((ψ g : κˣ) : κ) = gm r g 1 1 := fun g => rfl
  have hcp : ∀ g, (gm r g).charpoly = (gm σ g).charpoly * (X - C ((ψ g : κˣ) : κ)) := fun g =>
    charpoly_block _ (hb g)
  have hcσ : LinClosed (gm σ) := fun f =>
    hc (f ∘ₗ
      { toFun := fun M : Matrix (Fin 3) (Fin 3) κ => M.submatrix ![0, 2] ![0, 2]
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  obtain ⟨k, hk⟩ : ∃ k, α k = ψ u := by
    have h1 := congrArg (Polynomial.eval ((ψ u : κˣ) : κ)) ((hcp u).symm.trans hch)
    rw [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, eval_prod, eq_comm, Finset.prod_eq_zero_iff] at h1
    obtain ⟨k, -, hk⟩ := h1
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
    exact ⟨k, Units.ext hk.symm⟩
  have hch2 : (gm σ u).charpoly = ∏ i : Fin 2, (X - C ((α (k.succAbove i) : κˣ) : κ)) := by
    have h1 := (hcp u).symm.trans hch
    rw [Fin.prod_univ_succAbove _ k, hk, mul_comm] at h1
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) h1
  have hfree : FreeRatios ![α (k.succAbove 0), α (k.succAbove 1), ψ u] := by
    have e : ![α (k.succAbove 0), α (k.succAbove 1), ψ u] = α ∘ ![k.succAbove 0, k.succAbove 1, k] := by
      funext i
      fin_cases i <;> simp [hk]
    have inj : Function.Injective (![k.succAbove 0, k.succAbove 1, k] : Fin 3 → Fin 3) := by
      clear hk hch2 e
      revert k
      decide
    rw [e]
    exact fun i j hij => hα _ _ (inj.ne hij)
  obtain ⟨h, hh⟩ := regCosetE _ κ _ (ψ.comp (V ⊓ G').subtype) (strong_of G' V hV σ hcσ hirr) ⟨u, hu⟩
    (fun i => α (k.succAbove i)) hfree hch2 (σ s) (ψ s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  rw [hcp]
  simp only [gm, map_mul σ, map_mul ψ, Units.val_mul (σ s)]
  exact hh

private lemma charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, h2⟩ := hg s
  have h3 := Matrix.charpoly_of_upperTriangular ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    (fun i j hij => h1 i j hij)
  simp only [h2] at h3
  rw [← h3, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  rfl

end UpperTheory.V.Pr

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing in
theorem UpperTheory.V.Pr.nice_specialization_twist_satisfies_third_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → y.N3 := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hρ hψ U hU hne
  haveI : CompactSpace T.G.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact
  let r : T.G.G₀ →* GL (Fin n) y.Fb := W.pushRep (algebraMap y.Fr y.Fb) y.ρF
  have hr : ∀ g, gm r g = (W.mat y.ρF g).map (algebraMap y.Fr y.Fb) := fun g => rfl
  have hc : LinClosed (gm r) :=
    linClosedOfAdic T.G.G₀ y.A y.Fb ((algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr))
      ((algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)) n (fun g => W.mat y.ρ g) y.cont
  obtain ⟨v⟩ : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.big.1
    simp [Fr.Frame.d] at this
  have hsep : ∀ V : Subgroup T.G.G₀, IsOpen (V : Set T.G.G₀) → ∃ u ∈ V ⊓ T.G.G', ∃ α : Fin n → y.Fbˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : y.Fbˣ) : y.Fb)) := by
    intro V hV
    obtain ⟨g, hg, hfree⟩ := niceSep l O F n T x L y j hj hnice hρ hψ V hV v
    refine ⟨_, hg, fun i => Units.map (algebraMap y.Fr y.Fb).toMonoidHom
      (Units.map (algebraMap y.A y.Fr).toMonoidHom (y.ψ v i g)), fun a b hab m hm h => hfree a b hab m hm ?_, ?_⟩
    · refine Units.map_injective (f := (algebraMap y.Fr y.Fb).toMonoidHom) (algebraMap y.Fr y.Fb).injective ?_
      rw [map_pow, map_pow]
      exact h
    · have h1 : (W.mat y.ρF (T.G.φ v g)).charpoly = _ := charpoly_flag _ _ (y.flag v) g
      rw [hr, Matrix.charpoly_map, h1, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, map_X, map_C]
      rfl
  suffices h : ∃ σ ∈ U ∩ (T.G.G' : Set T.G.G₀), (gm r σ).charpoly.Separable by
    obtain ⟨σ, h1, h2⟩ := h
    rw [hr, Matrix.charpoly_map, Polynomial.separable_map] at h2
    exact ⟨σ, h1, h2⟩
  by_cases hE : n = 3 ∧ L.ρ.ee ≤ RingHom.ker j
  · obtain ⟨rfl, hE⟩ := hE
    have hz : ∀ g a b, Odd (Fr.w 3 a - Fr.w 3 b) → gm r g a b = 0 := by
      intro g a b hab
      have h1 : j (L.ρ.r (T.K.π g) a b) = 0 := hE (Ideal.subset_span ⟨_, a, b, hab, rfl⟩)
      have h2 : W.mat y.ρ g a b = 0 := by
        rw [hρ]
        show _ * j (L.ρ.r (T.K.π g) a b) = 0
        rw [h1, mul_zero]
      show algebraMap y.Fr y.Fb (algebraMap y.A y.Fr (W.mat y.ρ g a b)) = 0
      rw [h2, map_zero, map_zero]
    exact cosetE T.G.G' r hc
      (fun g => ⟨hz g 0 1 (by decide), hz g 1 0 (by decide), hz g 1 2 (by decide), hz g 2 1 (by decide)⟩)
      (niceIrrE l O F T x L y j hj hnice hρ hψ ⟨hnice.off, rfl, hE⟩) hsep U hU hne
  · exact cosetI (by rcases T.n23 with h | h <;> omega) T.G.G' r hc
      (niceIrr l O F n T x L y j hj hnice hρ hψ ⟨hnice.off, fun h3 h => hE ⟨h3, h⟩⟩) hsep U hU hne
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceTypeE
section
set_option linter.overlappingInstances false

open Matrix UpperTheory.V UpperTheory.V.W UpperTheory.V.U3

namespace UpperTheory.V.Pr

private def blk {H K : Type} [Group H] [CommRing K] (ρ : H →* GL (Fin 3) K)
    (hz : ∀ g, mat ρ g 0 1 = 0 ∧ mat ρ g 1 0 = 0 ∧ mat ρ g 1 2 = 0 ∧ mat ρ g 2 1 = 0) :
    H →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (mat ρ g).submatrix ![0, 2] ![0, 2]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
      map_mul' := fun g h => by
        obtain ⟨a1, a2, a3, a4⟩ := hz g
        obtain ⟨b1, b2, b3, b4⟩ := hz h
        ext i j
        simp only [map_mul, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        fin_cases i <;> fin_cases j <;>
          simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, a1, a2, a3, a4, b1, b2, b3, b4] }

private def mid {H K : Type} [Group H] [CommRing K] (ρ : H →* GL (Fin 3) K)
    (hz : ∀ g, mat ρ g 0 1 = 0 ∧ mat ρ g 1 0 = 0 ∧ mat ρ g 1 2 = 0 ∧ mat ρ g 2 1 = 0) :
    H →* GL (Fin 1) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (mat ρ g).submatrix ![1] ![1]
      map_one' := by
        ext i j
        fin_cases i; fin_cases j; simp
      map_mul' := fun g h => by
        obtain ⟨a1, a2, a3, a4⟩ := hz g
        ext i j
        simp only [map_mul, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        fin_cases i; fin_cases j
        simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, a2, a3] }

private def eqv : Fin 3 ≃ Fin 2 ⊕ Fin 1 where
  toFun := ![.inl 0, .inr 0, .inl 1]
  invFun := Sum.elim ![0, 2] ![1]
  left_inv := by decide
  right_inv := by decide

private theorem irr_one {H K : Type} [Group H] [Field K] (U : Subgroup H) (a : H → Matrix (Fin 1) (Fin 1) K) :
    MatIrr U a := by
  intro W _
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have h0 : v 0 ≠ 0 := fun h => hv0 (funext fun i => by fin_cases i; exact h)
    rw [eq_top_iff]
    intro u _
    have hu : u = (u 0 / v 0) • v := funext fun i => by
      fin_cases i
      simp [div_mul_cancel₀ _ h0]
    rw [hu]
    exact W.smul_mem _ hv

private theorem hom_zero {H K : Type} [Group H] [Field K] (U : Subgroup H) (a : H → Matrix (Fin 2) (Fin 2) K)
    (b : H → Matrix (Fin 1) (Fin 1) K) (h : MatIrr U a) (M : Matrix (Fin 1) (Fin 2) K)
    (hM : ∀ g ∈ U, M * a g = b g * M) : M = 0 := by
  have hinv : ∀ g ∈ U, ∀ v ∈ LinearMap.ker M.mulVecLin, a g *ᵥ v ∈ LinearMap.ker M.mulVecLin := by
    intro g hg v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases h _ hinv with hb | ht
  · have hv : ![M 0 1, -M 0 0] ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      ext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hb, Submodule.mem_bot] at hv
    have h1 := congrFun hv 0
    have h2 := congrFun hv 1
    simp at h1 h2
    ext i j
    fin_cases i
    fin_cases j <;> simp [h1, h2]
  · ext i j
    have hj : (Pi.single j 1 : Fin 2 → K) ∈ LinearMap.ker M.mulVecLin := by
      rw [ht]
      trivial
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hj
    have := congrFun hj i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

private theorem tw_form {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Fr.Frame l (IsLocalRing.ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
    {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (g : G.G₀) :
    (K.tw ρ g)ᵀ * Jmat A n * K.tw ρ (G.conj g) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) • Jmat A n := by
  have hc : ∀ h : F.G0, F.conj h = F.star h⁻¹ := fun h => by simp [Fr.Frame.star]
  have hr : (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g)) = Jmat A n := by
    rw [hc, ρ.pol]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ (Jmat A n) (Jmat A n), Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul,
      ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one, Matrix.one_mul]
  have hκ : (K.κA A g : A) * (K.κA A (G.conj g) : A) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
    have := congrArg (fun u : Oˣ => ((Units.map (algebraMap O A : O →* A) u : Aˣ) : A)) (K.κ_conj g)
    simp [TwLink.κA, GFrame.eps, pushCh, map_zpow] at this ⊢
    rw [this]
    rfl
  simp only [TwLink.tw, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    K.π_conj, hr, smul_smul]
  rw [← hκ, mul_comm]

private theorem blk_form {K : Type} [CommRing K] (X Y : Matrix (Fin 3) (Fin 3) K) (c : K)
    (hX : X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0) (hY : Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 1 2 = 0 ∧ Y 2 1 = 0)
    (h : Xᵀ * Jmat K 3 * Y = c • Jmat K 3) :
    (X.submatrix ![0, 2] ![0, 2])ᵀ * Jmat K 2 * Y.submatrix ![0, 2] ![0, 2] = c • Jmat K 2 ∧
    (X.submatrix ![1] ![1])ᵀ * Jmat K 1 * Y.submatrix ![1] ![1] = c • Jmat K 1 := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  obtain ⟨y1, y2, y3, y4⟩ := hY
  have he : ∀ i j, (Xᵀ * Jmat K 3 * Y) i j = (c • Jmat K 3) i j := fun i j => by rw [h]
  constructor
  · ext i j
    have := he (![0, 2] i) (![0, 2] j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three] at this ⊢
    fin_cases i <;> fin_cases j <;>
      simp [Jmat, x1, x2, x3, x4, y1, y2, y3, y4] at this ⊢ <;>
      linear_combination this
  · ext i j
    have := he 1 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fin.sum_univ_one, Fin.sum_univ_three] at this ⊢
    fin_cases i
    fin_cases j
    simp [Jmat, x1, x2, x3, x4, y1, y2, y3, y4] at this ⊢
    linear_combination this

private def JU (K : Type) [CommRing K] (n : ℕ) : GL (Fin n) K := ⟨Jmat K n, Jmat K n, Jmat_mul_Jmat n, Jmat_mul_Jmat n⟩

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.niceTypeE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → y.TypeE := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hmat hψ hTE
  have hee : L.ρ.ee ≤ RingHom.ker j := hTE.2.2
  have hz0 : ∀ g (i k : Fin 3), Odd (Fr.w 3 i - Fr.w 3 k) → mat y.ρ g i k = 0 := by
    intro g i k hodd
    have hm : L.ρ.r (T.K.π g) i k ∈ RingHom.ker j := hee (Ideal.subset_span ⟨_, i, k, hodd, rfl⟩)
    rw [RingHom.mem_ker] at hm
    rw [hmat]
    simp [TwLink.tw, Fr.NRep.map, hm]
  have hz : ∀ g, mat y.ρF g 0 1 = 0 ∧ mat y.ρF g 1 0 = 0 ∧ mat y.ρF g 1 2 = 0 ∧ mat y.ρF g 2 1 = 0 := by
    intro g
    have e : ∀ i k, Odd (Fr.w 3 i - Fr.w 3 k) → mat y.ρF g i k = 0 := fun i k h => by
      show algebraMap y.A y.Fr (mat y.ρ g i k) = 0
      rw [hz0 g i k h, map_zero]
    refine ⟨e 0 1 ?_, e 1 0 ?_, e 1 2 ?_, e 2 1 ?_⟩ <;> decide
  have hF : ∀ g, (mat y.ρF g)ᵀ * Jmat y.Fr 3 * mat y.ρF (T.G.conj g) =
      ((T.G.eps O y.Fr g ^ (1 - ((3 : ℕ) : ℤ)) : y.Frˣ) : y.Fr) • Jmat y.Fr 3 := by
    intro g
    have h := UpperTheory.V.Pr.tw_form T.K (L.ρ.map (j : L.R →+* y.A)) g
    rw [← hmat] at h
    have h2 := congrArg (fun M => M.map (algebraMap y.A y.Fr)) h
    have heps : (T.G.eps O y.Fr g ^ (1 - ((3 : ℕ) : ℤ)) : y.Frˣ) =
        Units.map (algebraMap y.A y.Fr : y.A →* y.Fr) (T.G.eps O y.A g ^ (1 - ((3 : ℕ) : ℤ))) := by
      rw [map_zpow]
      congr 1
    have hs : ∀ (c : y.A) (M : Matrix (Fin 3) (Fin 3) y.A),
        (c • M).map (algebraMap y.A y.Fr) = algebraMap y.A y.Fr c • M.map (algebraMap y.A y.Fr) := fun c M => by
      ext
      simp
    rw [heps]
    simp only [Matrix.map_mul, Matrix.transpose_map, Jmat_map] at h2
    rw [hs, Jmat_map] at h2
    exact h2
  have hB := fun g => UpperTheory.V.Pr.blk_form _ _ _ (hz g) (hz (T.G.conj g)) (hF g)
  have hb : ∀ g, mat (UpperTheory.V.Pr.blk y.ρF hz) g = (mat y.ρF g).submatrix ![0, 2] ![0, 2] := fun g => rfl
  have hm : ∀ g, mat (UpperTheory.V.Pr.mid y.ρF hz) g = (mat y.ρF g).submatrix ![1] ![1] := fun g => rfl
  have hirr := UpperTheory.V.Pr.niceIrrE l O F T x L y j hj hN hmat hψ hTE ⊤ isOpen_univ
  rw [top_inf_eq] at hirr
  have hirr1 : MatIrr T.G.G' (mat (pushRep (algebraMap y.Fr y.Fb) (UpperTheory.V.Pr.blk y.ρF hz))) := hirr
  refine ⟨2, 1, by norm_num, le_rfl, UpperTheory.V.Pr.eqv, 1, UpperTheory.V.Pr.blk y.ρF hz, UpperTheory.V.Pr.mid y.ρF hz,
    ?_, ⟨UpperTheory.V.Pr.JU _ 2, ?_⟩, ⟨UpperTheory.V.Pr.JU _ 1, ?_⟩, hirr1, UpperTheory.V.Pr.irr_one _ _, ?_⟩
  · intro g
    have h1 : ((1 * y.ρF g * 1⁻¹ : GL (Fin 3) y.Fr) : Matrix (Fin 3) (Fin 3) y.Fr) = mat y.ρF g := by
      simp [mat]
    obtain ⟨a1, a2, a3, a4⟩ := hz g
    rw [h1, hb, hm]
    ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k
    all_goals first
      | rfl
      | (simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
         first | exact a1 | exact a2 | exact a3 | exact a4)
  · intro g
    rw [hb, hb]
    exact (hB g).1
  · intro g
    rw [hm, hm]
    exact (hB g).2
  · intro M hM
    exact UpperTheory.V.Pr.hom_zero _ _ _ hirr1 M hM
end

