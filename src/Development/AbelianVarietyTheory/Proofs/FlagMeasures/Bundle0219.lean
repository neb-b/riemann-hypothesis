module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PairMove

open GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem aut_mul {n m : S.V ≃ₗ[E] S.V} (hm : IsAutLam S Λ m) (hn : IsAutLam S Λ n) : IsAutLam S Λ (m * n) := by
  refine ⟨Subgroup.mul_mem _ hm.1 hn.1, ?_⟩
  have key : ∀ y, (m * n) y ∈ Λ ↔ y ∈ Λ := fun y => by
    show m (n y) ∈ Λ ↔ y ∈ Λ
    rw [aut_mem_iff hm, aut_mem_iff hn]
  ext x
  rw [mem_gmap, ← key ((m * n).symm x), LinearEquiv.apply_symm_apply]

theorem aut_symm {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) : IsAutLam S Λ n.symm := by
  refine ⟨Subgroup.inv_mem _ hn.1, ?_⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm, aut_mem_iff hn]

theorem mem_iff_of_map {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) (x : S.V) : n x ∈ W ↔ x ∈ U := by
  rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem map_of_mem_iff {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : ∀ x, n x ∈ W ↔ x ∈ U) : U.map (n : S.V →ₗ[E] S.V) = W := by
  ext y
  rw [Submodule.mem_map_equiv, ← h (n.symm y), LinearEquiv.apply_symm_apply]

theorem map_symm {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) : W.map (n.symm : S.V →ₗ[E] S.V) = U := by
  ext y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  exact mem_iff_of_map h y

theorem orth_mem {n : S.V ≃ₗ[E] S.V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) {x : S.V} (hx : x ∈ orth S U) : n x ∈ orth S W := by
  have hn' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hn
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro w hw
  rw [← h] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  show S.hT (n u) (n x) = 0
  rw [hn']
  exact hx u hu

theorem lrep_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ Lrep Λ F) : n x ∈ Lrep Λ G := by
  simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, orth_mem hn.1 h hx.2⟩

theorem xlam_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ XLam Λ F) : n x ∈ XLam Λ G := by
  simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, (mem_iff_of_map h x).2 hx.2⟩

theorem ngx_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    {x : S.V} (hx : x ∈ NgX Λ g F F') : n x ∈ NgX Λ g G G' := by
  have hΛ : Λ.map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ := hn.2
  have hle : (NgX Λ g F F').map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) ≤ NgX Λ g G G' := by
    rw [NgX, NgX, Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', hΛ]
    refine sup_le_sup (sup_le_sup le_rfl ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h hy
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h' hy
  exact hle (Submodule.mem_map_of_mem hx)

theorem ngx_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    (x : S.V) : n x ∈ NgX Λ g G G' ↔ x ∈ NgX Λ g F F' := by
  constructor
  · intro hx
    have := ngx_mem (aut_symm hn) (map_symm h) (map_symm h') g hx
    rwa [LinearEquiv.symm_apply_apply] at this
  · exact ngx_mem hn h h' g

theorem nlam_map {n : S.V ≃ₗ[E] S.V} {F : LFlag S r T} (hn : n ∈ NLam Λ F) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := by
  have key : ∀ m ∈ NLam Λ F, ∀ x ∈ Xsp F, m x ∈ Xsp F := by
    intro m hm x hx
    rw [← sub_add_cancel (m x) x]
    exact add_mem (hm.2.2 x (X_le_orth hx)) hx
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key n hn x hx
  · intro x hx
    exact ⟨n.symm x, key _ (symm_mem_NLam hn) x hx, by simp⟩

theorem xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  rw [show {i : Fin r | i.1 < r} = Set.univ from Set.eq_univ_of_forall fun i => i.2, Set.image_univ]

theorem finrank_X (F : LFlag S r T) : finrank E (Xsp F) = r := by
  show finrank E (Submodule.span E (Set.range F.fl.e)) = r
  rw [finrank_span_eq_card F.fl.e_indep, Fintype.card_fin]

theorem frame_move {n : S.V ≃ₗ[E] S.V} {F A : LFlag S r T} {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (h3 : frame A = frameAct (fun a => n (frame F a)) ξ) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A ∧ n F.fl.z - A.fl.z ∈ Xsp A := by
  have hFe : ∀ i : Fin r, frame F i.castSucc = F.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z i.castSucc = F.fl.e i
    simp
  have hAe : ∀ i : Fin r, frame A i.castSucc = A.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z i.castSucc = A.fl.e i
    simp
  have hFz : frame F (Fin.last r) = F.fl.z := by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) = F.fl.z
    simp
  have hAz : frame A (Fin.last r) = A.fl.z := by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z (Fin.last r) = A.fl.z
    simp
  have hmem : ∀ i : Fin r, n (frame F i.castSucc) ∈ (Xsp F).map (n : S.V →ₗ[E] S.V) := fun i =>
    Submodule.mem_map_of_mem (by rw [hFe]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hX : Xsp A ≤ (Xsp F).map (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range A.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← hAe j, h3]
    simp only [frameAct, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : j.castSucc < a
    · rw [h1 a j.castSucc ha]
      simp
    · have hne : a ≠ Fin.last r := by
        rintro rfl
        exact ha (Fin.castSucc_lt_last j)
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hne
      exact Submodule.smul_mem _ _ (hmem i)
  have hF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A := by
    have : FiniteDimensional E (Xsp F) := FiniteDimensional.span_of_finite E (Set.finite_range _)
    symm
    apply Submodule.eq_of_le_of_finrank_eq hX
    rw [LinearEquiv.finrank_map_eq, finrank_X, finrank_X]
  refine ⟨hF, ?_⟩
  rw [← hAz, h3]
  simp only [frameAct]
  rw [Fin.sum_univ_castSucc, h2 (Fin.last r), hFz]
  have hs : ∑ i : Fin r, ((ξ i.castSucc (Fin.last r) : 𝓞 E) : E) • n (frame F i.castSucc) ∈ Xsp A := by
    rw [← hF]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  have e : ((1 : 𝓞 E) : E) • n F.fl.z = n F.fl.z := by simp
  rw [e, sub_add_eq_sub_sub_swap, sub_self, zero_sub]
  exact neg_mem hs

theorem move {g : ℕ} {F : LFlag S r T} {F' F'' A B : LFlag S r T'} {β n' n'' : S.V ≃ₗ[E] S.V}
    (hp : IsPair Λ F F' F'' β g) (hn' : n' ∈ NLam Λ F) (hn'' : n'' ∈ NLam Λ F)
    (hA : (Xsp F').map (n' : S.V →ₗ[E] S.V) = Xsp A) (zA : n' F'.fl.z - A.fl.z ∈ Xsp A)
    (hB : (Xsp F'').map (n'' : S.V →ₗ[E] S.V) = Xsp B) (zB : n'' F''.fl.z - B.fl.z ∈ Xsp B) :
    IsAutLam S Λ (n'' * β * n'⁻¹) ∧
      (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B ∧
      (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  have hn'A : IsAutLam S Λ n' := hn'.1
  have hn''A : IsAutLam S Λ n'' := hn''.1
  obtain ⟨hβ, hβF, hβz, hι⟩ := hp
  have hγ : ∀ x, (n'' * β * n'⁻¹) x = n'' (β (n'.symm x)) := fun x => rfl
  have hβX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    have := hβF r
    rwa [xflag_top, xflag_top] at this
  have hAB : (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B := by
    apply map_of_mem_iff
    intro x
    rw [hγ, mem_iff_of_map hB, mem_iff_of_map hβX, mem_iff_of_map (map_symm hA)]
  have hFn' : (Xsp F).map (n' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn'
  have hFn'' : (Xsp F).map (n'' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn''
  refine ⟨aut_mul (aut_mul hn''A hβ) (aut_symm hn'A), hAB, ?_, ?_⟩
  · have e : (n'' * β * n'⁻¹) A.fl.z - B.fl.z =
        (n'' F''.fl.z - B.fl.z) - (n'' * β * n'⁻¹) (n' F'.fl.z - A.fl.z) := by
      simp only [hγ, map_sub, LinearEquiv.symm_apply_apply, hβz]
      abel
    rw [e]
    exact sub_mem zB (by rw [← hAB]; exact Submodule.mem_map_of_mem zA)
  · intro x' hx' l hl
    have hy : n'.symm x' ∈ Lrep Λ F' := lrep_mem (aut_symm hn'A) (map_symm hA) hx'
    have hm : n'.symm l ∈ Lrep Λ F := lrep_mem (aut_symm hn'A) (map_symm hFn') hl
    simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hl
    have h1 : l - x' ∈ NgX Λ g F A ↔ n'.symm l - n'.symm x' ∈ NgX Λ g F F' := by
      rw [← ngx_iff hn'A hFn' hA g, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have h3 : n'.symm l - β (n'.symm x') ∈ NgX Λ g F F'' ↔
        n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [hγ x', ← ngx_iff hn''A hFn'' hB g, map_sub]
    have hd : l - n'' (n'.symm l) ∈ NgX Λ g F B := by
      obtain ⟨hνA, -, hνo⟩ := mul_mem_NLam (symm_mem_NLam hn') hn''
      have e1 : n'' (n'.symm l) - l ∈ XLam Λ F := by
        simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem]
        exact ⟨sub_mem ((aut_mem_iff hνA l).2 hl.1) hl.1, hνo l hl.2⟩
      have e2 : n'' (n'.symm l) - l ∈ NgX Λ g F B := by
        rw [NgX]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right e1)
      rw [← neg_sub]
      exact neg_mem e2
    have h4 : n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B ↔
        l - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [show l - (n'' * β * n'⁻¹) x' = (n'' (n'.symm l) - (n'' * β * n'⁻¹) x') + (l - n'' (n'.symm l)) by abel]
      exact (add_mem_cancel_right hd).symm
    exact h1.trans ((hι _ hy _ hm).trans (h3.trans h4))

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pair_move : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  intro D T T' Λ g F F' F'' A B β n' n'' hp hn' hn'' hA hB
  obtain ⟨ξ, h1, h2, h3⟩ := hA
  obtain ⟨η, k1, k2, k3⟩ := hB
  obtain ⟨a1, a2⟩ := frame_move h1 h2 h3
  obtain ⟨b1, b2⟩ := frame_move k1 k2 k3
  exact move hp hn' hn'' a1 a2 b1 b2

end GlobalTheory.LoopC.PairMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.DetMap

section General

variable {R K U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem length_quot_map (f : U →ₗ[R] V) (hf : Function.Injective f) (A B : Submodule R U) :
    Module.length R ((A.map f) ⧸ (B.map f).comap (A.map f).subtype) =
      Module.length R (A ⧸ B.comap A.subtype) := by
  let e : A ≃ₗ[R] A.map f := Submodule.equivMapOfInjective f hf A
  have he : (B.comap A.subtype).map (e : A →ₗ[R] A.map f) = (B.map f).comap (A.map f).subtype := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, haB, rfl⟩
      exact ⟨a, haB, rfl⟩
    · intro hz
      obtain ⟨b, hb, hbz⟩ := hz
      obtain ⟨a, ha, haz⟩ := z.2
      obtain rfl : a = b := hf (haz.trans hbz.symm)
      exact ⟨⟨a, ha⟩, hb, Subtype.ext haz⟩
  exact (Submodule.Quotient.equiv _ _ e he).length_eq.symm

theorem localization_map₂ (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A : Submodule R U) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (i.restrictScalars R)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (i.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := hRK (by rw [h0, map_zero])
      rw [this]
      exact p.zero_mem
    refine ⟨(algebraMap R K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • a), smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · rw [LinearMap.restrictScalars_apply] at hax ⊢
      rw [map_smul, hax, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hsy⟩, rfl⟩
    exact ⟨s, hs, s • y, hsy, LinearMap.map_smul _ s y⟩

theorem locLen_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.locLen p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B,
    length_quot_map (i.restrictScalars R) (by simpa using hi)]

theorem lidx_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.lidx p A B := by
  have hi' : Function.Injective (i.restrictScalars R) := by simpa using hi
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [← Submodule.map_inf _ hi', locLen_map hRK i hi, locLen_map hRK i hi]

end General

section NumberField

variable {K U V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genIdxH_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    genIdxH (A.map (i.restrictScalars (𝓞 K))) (B.map (i.restrictScalars (𝓞 K))) = genIdxH A B := by
  have hRK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  unfold genIdxH
  refine finprod_congr fun P => ?_
  haveI := P.isPrime
  rw [lidx_map hRK i hi]

theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem dualInH_map (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V)
    (hiso : ∀ x y, hV (i x) (i y) = hU x y) (N : Submodule (𝓞 K) U) :
    dualInH hV (N.map (i.restrictScalars (𝓞 K))) =
      (dualInH hU N).map (i.restrictScalars (𝓞 K)) := by
  have hspan : (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span K (N : Set U)).map i := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  simp only [dualInH, Submodule.mem_inf, Submodule.restrictScalars_mem, hspan, mem_dual,
    Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨y, ⟨fun n hn => ?_, hy⟩, rfl⟩
    rw [← hiso]
    exact hx (i n) ⟨n, hn, rfl⟩
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    rw [hiso]
    exact hy n hn

end NumberField

theorem latDetH_map : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  intro K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N
  unfold latDetH
  rw [dualInH_map hU hV i hiso, genIdxH_map i hi]

end GlobalTheory.LoopC.DetMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem isClosed_flagM {n a : ℕ} (ε : Fin n → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed (flagM ε W) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g := Units.continuous_val.comp continuous_subtype_val
  have hc' : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ := hc.matrix_conjTranspose
  have hset : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp [flagM]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  have hW : IsClosed (W i : Set (Fin n → ℂ)) := (W i).closed_of_finiteDimensional
  exact (hW.preimage (hc.matrix_mulVec continuous_const)).inter (hW.preimage (hc'.matrix_mulVec continuous_const))

theorem ae_det_ne_zero {a : ℕ} (j : Fin a → ℕ) (d : Fin a → ℝ) {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    [SFinite ν] :
    ∀ᵐ z ∂((Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)).prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 := by
  have h1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)), ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h0 : ∀ᵐ y ∂(ENNReal.ofReal (d i) • haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      have hn := (haarLoc_conj_and_null (j i)).2
      rw [ae_iff, Measure.smul_apply]
      simp [hn]
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => ENNReal.ofReal (d i) • haarLoc (j i)) (i := i)).eventually
      (p := fun y => (Matrix.of y).det ≠ 0) h0
  exact Measure.quasiMeasurePreserving_fst.ae h1

private theorem measurePreserving_smul_measure {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) (c : ENNReal) : MeasurePreserving f (c • μ) (c • μ) :=
  ⟨hf.measurable, by rw [Measure.map_smul c hf.measurable.aemeasurable, hf.map_eq]⟩

theorem map_chart_carried_and_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  intro n n₀ a j ε ε₀ B B₀ hB W hW θ hθ hθl c
  set P := Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i) with hP
  set ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀ with hν
  have hdet : ∀ᵐ z ∂(P.prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 :=
    ae_det_ne_zero j (fun i => 2 ^ (j i ^ 2)) ν
  have hmem : ∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀,
      (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → θ z ∈ flagM ε W := fun z hz =>
    (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW (θ z)).2 ⟨fun i => Matrix.of (z.1 i), z.2, hz, hθl z hz⟩
  have hM : MeasurableSet (flagM ε W) := (isClosed_flagM ε W).measurableSet
  refine ⟨?_, fun s hs => ?_⟩
  · have h : ∀ᵐ m ∂((P.prod ν).map θ), m ∈ flagM ε W :=
      (ae_map_iff hθ.aemeasurable hM).2 (hdet.mono hmem)
    exact measure_mono_null (fun m hm => hm) (ae_iff.1 h)
  · obtain ⟨x, g, hx, hs'⟩ := (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW s).1 hs
    let T : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
      Prod.map (fun (y : ∀ i, Fin (j i) → Fin (j i) → ℂ) (i : Fin a) (r t : Fin (j i)) =>
        (x i * Matrix.of (y i) * (1 : Matrix (Fin (j i)) (Fin (j i)) ℂ)) r t) (fun u => g * u)
    have hT : MeasurePreserving T (P.prod ν) (P.prod ν) := by
      refine MeasurePreserving.prod ?_ ?_
      · exact measurePreserving_pi _ _ fun i =>
          measurePreserving_smul_measure (GlobalTheory.HaarMul.measurePreserving_mul_mul (j i) (x i) 1 (hx i) (by simp)) _
      · exact measurePreserving_smul_measure (measurePreserving_mul_left (Formalism.REAL.muG ε₀) g) _
    have hcomm : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → s * θ z = θ (T z) := by
      intro z hz
      have hz' : ∀ i, (Matrix.of ((T z).1 i)).det ≠ 0 := by
        intro i
        have : Matrix.of ((T z).1 i) = x i * Matrix.of (z.1 i) := by
          ext r t
          simp [T]
        rw [this, Matrix.det_mul]
        exact mul_ne_zero (hx i) (hz i)
      apply Subtype.ext
      apply Units.ext
      change uMat s * uMat (θ z) = uMat (θ (T z))
      rw [hs', hθl z hz, hθl (T z) hz', ← hB.lev_mul]
      congr 1
      · funext i
        ext r t
        simp [T]
    have hmul : Measurable fun m : Formalism.REAL.UJ ε => s * m := measurable_const_mul s
    calc ((P.prod ν).map θ).map (fun m => s * m)
        = (P.prod ν).map (fun z => s * θ z) := by rw [Measure.map_map hmul hθ]; rfl
      _ = (P.prod ν).map (fun z => θ (T z)) := Measure.map_congr (hdet.mono fun z hz => hcomm z hz)
      _ = ((P.prod ν).map T).map θ := by rw [Measure.map_map hθ hT.measurable]; rfl
      _ = (P.prod ν).map θ := by rw [hT.map_eq]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanLEqOfRealMeanCRe
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem meanL_eq_ofReal_meanC_re (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G)
    (ι : Type) [Countable ι] (f : ι → G → ℝ) (hm : ∀ i, Measurable (f i))
    (h0 : ∀ i h, 0 ≤ f i h) (hF : μ 𝓕 < ⊤)
    (hI : ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤) :
    meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) =
      ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  set S : G → ℝ≥0∞ := fun h => ∑' i, ENNReal.ofReal (f i h) with hSdef
  have hnorm : ∀ i h, ‖((f i h : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (f i h) := by
    intro i h
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (h0 i h)]
  have hS : ∫⁻ h in 𝓕, S h ∂μ < ⊤ := by
    simpa only [hnorm] using hI
  have hSm : Measurable S := Measurable.tsum (fun i => (hm i).ennreal_ofReal)
  have hae : ∀ᵐ h ∂(μ.restrict 𝓕), S h < ⊤ := ae_lt_top hSm hS.ne
  have hint : ∫ h in 𝓕, (∑' i, ((f i h : ℝ) : ℂ)) ∂μ = (((∫⁻ h in 𝓕, S h ∂μ).toReal : ℝ) : ℂ) := by
    have hcongr : (fun h => ∑' i, ((f i h : ℝ) : ℂ)) =ᵐ[μ.restrict 𝓕]
        fun h => (((S h).toReal : ℝ) : ℂ) := by
      filter_upwards [hae] with h hh
      have hsum : Summable (fun i => f i h) := by
        convert ENNReal.summable_toReal hh.ne using 1
        funext i
        exact (ENNReal.toReal_ofReal (h0 i h)).symm
      show _ = (((∑' i, ENNReal.ofReal (f i h)).toReal : ℝ) : ℂ)
      rw [← Complex.ofReal_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i h) hsum,
        ENNReal.toReal_ofReal (tsum_nonneg (fun i => h0 i h))]
    rw [integral_congr_ae hcongr, integral_complex_ofReal, integral_toReal hSm.aemeasurable hae]
  unfold meanL meanC
  rw [hint, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  by_cases hz : μ 𝓕 = 0
  · have hr : μ.restrict 𝓕 = 0 := Measure.restrict_eq_zero.mpr hz
    simp [hr, hz]
  · rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hS.ne,
      ← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hz)]

end GlobalTheory
end

