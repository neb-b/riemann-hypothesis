module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomlDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homl_desc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ'), Continuous f → Function.Surjective f → Finite (HomL l (H.comap f)) → Finite (HomL l H) ∧ Nat.card (HomL l H) ≤ Nat.card (HomL l (H.comap f)) := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H hf hsurj hfin
  let g : (H.comap f) →* H := f.subgroupComap H
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  let Φ : HomL l H → HomL l (H.comap f) := fun φ =>
    ⟨φ.1.comp g, by
      show IsOpen (g ⁻¹' (φ.1.ker : Set H))
      exact φ.2.preimage hg⟩
  have hinj : Function.Injective Φ := by
    intro φ ψ h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hgs y
    have := congrArg (fun χ : HomL l (H.comap f) => χ.1 x) h
    simpa [Φ] using this
  have hF : Finite (HomL l H) := Finite.of_injective Φ hinj
  exact ⟨hF, Nat.card_le_card_of_injective Φ hinj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KerOo
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem isOpen_map_of_ker_le {P Z : Type} [Group P] [TopologicalSpace P] [CompactSpace P]
    [Group Z] [TopologicalSpace Z] [T2Space Z] (f : P →* Z) (hf : Continuous f) (hs : Function.Surjective f)
    (V : Subgroup P) (hV : IsOpen (V : Set P)) (hk : f.ker ≤ V) : IsOpen (V.map f : Set Z) := by
  rw [← (hf.isClosedMap.isQuotientMap hf hs).isOpen_preimage]
  have : f ⁻¹' (V.map f : Set Z) = V := by
    rw [← Subgroup.coe_comap, Subgroup.comap_map_eq_self hk]
  rw [this]; exact hV

theorem UpperTheory.V.Pa.ker_oo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T), T.ProL → Λ.h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure := by
  intro l _ L G0 T Λ hT x hx
  set K := (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure with hK
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  refine (totallyDisconnected_quot Λ.G.Γ K (Subgroup.isClosed_topologicalClosure _)).2 x fun O => ?_
  haveI := O.isNormal'
  set W : Subgroup Λ.G.Γ := K ⊔ O.toSubgroup with hW
  haveI hWn : W.Normal := Subgroup.sup_normal _ _
  have hWo : IsOpen (W : Set Λ.G.Γ) := Subgroup.isOpen_mono (le_sup_right : O.toSubgroup ≤ W) O.isOpen'
  have hta : ∀ j, (Λ.ta j : Λ.G.Γ) ∈ W := fun j =>
    Subgroup.mem_sup_left (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨j, rfl⟩))
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := W.comap Λ.πo, isOpen' := hWo.preimage Λ.πo_cont, isNormal' := hWn.comap _ }
  have hVn : V.toSubgroup.Normal := V.isNormal'
  have hVo : IsOpen (V.toSubgroup : Set Λ.Ph) := V.isOpen'
  have hko : Λ.πo.ker ≤ V.toSubgroup := fun g hg => by
    show Λ.πo g ∈ W
    rw [MonoidHom.mem_ker.1 hg]; exact W.one_mem
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG0 : TopFG G0.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 G0.Γ (Λ.h.p.comp Λ.πo) (Λ.h.cont.comp Λ.πo_cont)
    (Λ.h.surj.comp Λ.πo_surj)
  have hidx : V.toSubgroup.index ≠ 0 := by
    haveI : Finite (Λ.Ph ⧸ V.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hVo
    exact Subgroup.index_ne_zero_of_finite
  have hfin := (finite_hom_of_topFG G0.Γ hG0).2.2 _ hidx
  have hall : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ A ∈ {H : Subgroup G0.Γ | IsOpen (H : Set G0.Γ) ∧ H.index = V.toSubgroup.index},
      A.Normal → ∀ g, (T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹ ∈ A := by
    rw [hfin.eventually_all]
    intro A hA
    by_cases hn : A.Normal
    · exact (Λ.p_lim { toSubgroup := A, isOpen' := hA.1, isNormal' := hn }).mono fun N h _ => h
    · exact Eventually.of_forall fun N h => absurd h hn
  obtain ⟨N, h1, h2, h3⟩ := ((Λ.ker_lim V).and ((Λ.ta_lim V).and hall)).exists
  have hkN : (Λ.π N).ker ≤ V.toSubgroup := le_sup_left.trans (h1.le.trans (sup_le hko le_rfl))
  haveI hVNn : (V.toSubgroup.map (Λ.π N)).Normal := hVn.map _ (Λ.π_surj N)
  have hVNo := isOpen_map_of_ker_le (Λ.π N) (Λ.π_cont N) (Λ.π_surj N) _ hVo hkN
  have hkh : (T.h N).p.ker ≤ V.toSubgroup.map (Λ.π N) := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_of_isOpen _ hVNo))
    rw [hT.2 N, sup_bot_eq]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, g', hg, hg', hgg⟩ := h2 j
    have hg'V : g' ∈ V.toSubgroup := by
      show Λ.πo g' ∈ W
      rw [hg']; exact hta j
    refine ⟨g, ?_, hg⟩
    have := mul_mem hg'V (inv_mem hgg)
    simpa using this
  let f : Λ.Ph →* G0.Γ := (T.h N).p.comp (Λ.π N)
  have hfs : Function.Surjective f := (T.h N).surj.comp (Λ.π_surj N)
  have hfk : f.ker ≤ V.toSubgroup := fun g hg => by
    rw [← Subgroup.comap_map_eq_self hkN]
    exact hkh hg
  have hAo := isOpen_map_of_ker_le f ((T.h N).cont.comp (Λ.π_cont N)) hfs _ hVo hfk
  have hAi : (V.toSubgroup.map f).index = V.toSubgroup.index := by
    rw [← Subgroup.index_comap_of_surjective _ hfs, Subgroup.comap_map_eq_self hfk]
  obtain ⟨g, rfl⟩ := Λ.πo_surj x
  have h4 := h3 _ ⟨hAo, hAi⟩ (hVn.map _ hfs) g
  rw [MonoidHom.mem_ker.1 hx, inv_one, mul_one] at h4
  have h5 : g ∈ (V.toSubgroup.map f).comap f := h4
  rw [Subgroup.comap_map_eq_self hfk] at h5
  exact h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapStar
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ms_single {B X Y : Type} [CommRing B] [Group X] [Group Y] (f : X →* Y) (a : X) (c : B) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem ms_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a : F.G₀) (c : B) :
    F.star O B n (MonoidAlgebra.single a c) =
      MonoidAlgebra.single (F.conj a)⁻¹ (c * ((F.eps O B a ^ (1 - (n : ℤ)) : Bˣ) : B)) := by
  unfold GFrame.star GFrame.starOp
  rw [MonoidAlgebra.lift_single, MulOpposite.unop_smul]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, MonoidAlgebra.smul_single, smul_eq_mul]

private theorem ms_add {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a b : MonoidAlgebra B F.G₀) :
    F.star O B n (a + b) = F.star O B n a + F.star O B n b := by
  unfold GFrame.star
  rw [map_add (f := _), MulOpposite.unop_add]

private theorem ms_zero {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) : F.star O B n 0 = 0 := by
  unfold GFrame.star
  rw [map_zero, MulOpposite.unop_zero]

theorem UpperTheory.V.Pa.map_star :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B], (∀ y, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.star O B n y) = G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B g.p₀ y)) ∧ (∀ v (ψ : Fin n → L.Gv v →* Bˣ) a, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.oEl v ψ a) = G'.frame.oEl v ψ a) ∧ (∀ (ph : G.G₀) (U : Fin n → B), MonoidAlgebra.mapDomainRingHom B g.p₀ (q1El ph U) = q1El (g.p₀ ph) U) ∧ ∀ (ph ta : G.G₀) (U : Fin n → B) i y, MonoidAlgebra.mapDomainRingHom B g.p₀ (q2El ph ta U i y) = q2El (g.p₀ ph) (g.p₀ ta) U i y := by
  intro l _ L G G' g n O _ _ B _ _
  refine ⟨fun y => ?_, fun v ψ a => ?_, fun ph U => ?_, fun ph ta U i y => ?_⟩
  · induction y using MonoidAlgebra.induction_linear with
    | zero => rw [ms_zero, map_zero, ms_zero]
    | add a b ha hb => rw [ms_add, map_add (f := _), map_add (f := _), ms_add, ha, hb]
    | single a c =>
      rw [ms_star, ms_single, ms_single, ms_star, map_inv, g.p₀_conj, g.eps_p₀]
  · unfold GFrame.oEl
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one, g.p₀_φ]
  · unfold q1El
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one]
  · unfold q2El
    rw [map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2
      funext k
      simp only [Function.comp_apply]
      split_ifs
      · exact map_one _
      · simp only [map_sub, ms_single, map_one]
    · simp only [map_sub, ms_single, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.OdComm
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem comm_of_sep {K V : Type} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g h : Module.End K V) (hs : f.charpoly.Separable)
    (hg : Commute f g) (hh : Commute f h) : g * h = h * g := by
  classical
  have key : ∀ μ : K, ∀ x ∈ f.maxGenEigenspace μ, (g * h) x = (h * g) x := by
    intro μ x hx
    have hd : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hd
    have hgW := Module.End.mapsTo_maxGenEigenspace_of_comm hg μ
    have hhW := Module.End.mapsTo_maxGenEigenspace_of_comm hh μ
    obtain ⟨a, ha⟩ := hv ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hv ⟨g (v : V), hgW v.2⟩
    obtain ⟨c, hc⟩ := hv ⟨h (v : V), hhW v.2⟩
    have ha' : a • (v : V) = x := congrArg Subtype.val ha
    have hb' : b • (v : V) = g v := congrArg Subtype.val hb
    have hc' : c • (v : V) = h v := congrArg Subtype.val hc
    rw [← ha', Module.End.mul_apply, Module.End.mul_apply, map_smul, map_smul, map_smul, map_smul,
      ← hb', ← hc', map_smul, map_smul, ← hb', ← hc', smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hker : ∀ μ, f.maxGenEigenspace μ ≤ LinearMap.ker (g * h - h * g) := by
    intro μ x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact key μ x hx
  have htop : LinearMap.ker (g * h - h * g) = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top f]
    exact iSup_le hker
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp htop)

private theorem mat_comm_of_sep {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (P Z E : Matrix (Fin n) (Fin n) K) (hs : P.charpoly.Separable)
    (hg : P * Z = Z * P) (hh : P * E = E * P) : Z * E = E * Z := by
  let φ := (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K))
  have hc : (φ P).charpoly = P.charpoly := Matrix.charpoly_toLin' P
  have e := comm_of_sep (φ P) (φ Z) (φ E) (by rw [hc]; exact hs)
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hg])
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hh])
  apply φ.injective
  rw [map_mul, map_mul]
  exact e

theorem UpperTheory.V.Pa.od_comm :
    ∀ (A : Type) [CommRing A] [IsDomain A] (n a : ℕ) (P Z : Matrix (Fin n) (Fin n) A) (al : Fin n → A), P ∈ Ev A A n a → Z ∈ Od A A n a → Function.Injective al → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → P * Z = Z * P → Z = 0 := by
  intro A _ _ n a P Z al hP hZ hal hchar hPZ
  classical
  have hP' : ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → P i j = 0 := by
    intro i j h
    have := (hP i j).2 h
    simpa using this
  have hZ' : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
    intro i j h
    have := (hZ i j).1 h
    simpa using this
  let e : Fin n → A := fun i => if (i : ℕ) < a then 1 else 0
  have hPE : P * Matrix.diagonal e = Matrix.diagonal e * P := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · simp [e, hi, hj]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj]
  let K := AlgebraicClosure (FractionRing A)
  let ι : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hs : (P.map ι).charpoly.Separable := by
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (hι.comp hal)
  have h1 : P.map ι * Z.map ι = Z.map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPZ]
  have h2 : P.map ι * (Matrix.diagonal e).map ι = (Matrix.diagonal e).map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPE]
  have h3 := mat_comm_of_sep (P.map ι) (Z.map ι) ((Matrix.diagonal e).map ι) hs h1 h2
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h3
  have h4 : Z * Matrix.diagonal e = Matrix.diagonal e * Z := Matrix.map_injective hι h3
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h5
  rw [Matrix.zero_apply]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
  · exact hZ' i j (by simp [hi, hj])
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5.symm
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5
  · exact hZ' i j (by simp [hi, hj])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlChBar
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_prime_power_pow_eq_one (l n N : ℕ) {B E : Type} [CommRing B] [Ring E] [Algebra B E] (m : Ideal B)
    (hN : ∀ a ∈ m ^ N, algebraMap B E a = 0) (hl : (l : B) ∈ m) (x : E) (p : Polynomial B)
    (hp : Polynomial.aeval x p = 0) (hc : ∀ i, (p - (Polynomial.X - 1) ^ n).coeff i ∈ m) :
    ∃ e : ℕ, x ^ l ^ e = 1 := by
  let K : Ideal (Polynomial B) := RingHom.ker (Polynomial.aeval x : Polynomial B →ₐ[B] E)
  have hm : m.map Polynomial.C ≤ K.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine ⟨N, ?_⟩
    show Polynomial.aeval x (Polynomial.C a ^ N) = 0
    rw [← map_pow, Polynomial.aeval_C]
    exact hN _ (Ideal.pow_mem_pow ha N)
  have h1 : (Polynomial.X - 1 : Polynomial B) ∈ K.radical := by
    have h2 : p ∈ K.radical := Ideal.le_radical hp
    have h3 := K.radical.sub_mem h2 (hm (Ideal.mem_map_C_iff.2 hc))
    rw [sub_sub_cancel] at h3
    exact Ideal.mem_radical_of_pow_mem h3
  have h2 : (l : Polynomial B) ∈ K.radical := by
    have := hm (Ideal.mem_map_of_mem Polynomial.C hl)
    rwa [map_natCast] at this
  let J : Ideal (Polynomial B) := Ideal.span {(l : Polynomial B), Polynomial.X - 1}
  have hJ : J ≤ K.radical := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact h2
    · exact h1
  obtain ⟨j, hj⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (Submodule.fg_span (Set.toFinite _))
  have h4 := pow_mem_of_sub_one_mem l (Polynomial B) J.toTwoSided
    (Ideal.mem_toTwoSided.2 (Ideal.subset_span (by simp))) j Polynomial.X
    (Ideal.mem_toTwoSided.2 (Ideal.subset_span (by simp)))
  rw [Ideal.asIdeal_toTwoSided] at h4
  have h5 : Polynomial.aeval x ((Polynomial.X : Polynomial B) ^ l ^ j - 1) = 0 :=
    hj (Ideal.pow_le_pow_right (Nat.le_succ j) h4)
  refine ⟨j, ?_⟩
  simpa [sub_eq_zero] using h5

private theorem ch_mem {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    Polynomial.aeval y (D.chi y) ∈ TwoSidedIdeal.span D.CH := by
  rw [← UpperTheory.V.CA.d_toDet_CH]
  have h1 := (UpperTheory.V.CA.d_chS D.toDet A).1 (1 ⊗ₜ y)
  have h2 : D.toDet.chiS A (1 ⊗ₜ y) = D.chi y := by
    show D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    rw [map_sub, Algebra.TensorProduct.map_tmul, ofT_tmul, ofT_tmul, map_one, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  rw [h2] at h1
  have key : ∀ w ∈ Submodule.span A ((fun z : MonoidAlgebra A G => (1 : A) ⊗ₜ[A] z) '' (D.toDet.CH : Set (MonoidAlgebra A G))),
      Algebra.TensorProduct.lid A (MonoidAlgebra A G) w ∈ D.toDet.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      simpa using hz
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  have h3 := key _ h1
  rw [← Polynomial.aeval_algHom_apply] at h3
  simpa using h3

private theorem chi_diag {n : ℕ} {k G : Type} [CommRing k] [Group G] (χ : Fin n → G →* kˣ) (g : G)
    (h : ∀ i, χ i g = 1) :
    (GDet.ofRep (diagRep χ)).chi (MonoidAlgebra.single g 1) = (Polynomial.X - 1) ^ n := by
  show (GDet.repAlg (diagRep χ) (Polynomial k) _).det = _
  have : GDet.repAlg (diagRep χ) (Polynomial k) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)) =
      diagonal fun _ => Polynomial.X - 1 := by
    have e : diagRep χ g = 1 := by
      show diagonal (fun i => (χ i g : k)) = 1
      simp [h]
    ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, e, hab]
  rw [this, det_diagonal]
  simp

theorem UpperTheory.V.Pa.pl_chBar :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → ∀ (Z : Set (MonoidAlgebra B G.G₀)) (k : G.G₀), (k : G.Γ) ∈ PL l H → MonoidAlgebra.single k 1 - 1 ∈ u.D.chBar Z := by
  intro l _ L G n O _ _ _ hO _ r B _ _ _ u H _ _ hH hχ Z k hk
  simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
  intro N V
  generalize hS : (u.D.CH ∪ Z ∪ _ ∪ _ : Set (MonoidAlgebra B G.G₀)) = S
  let I := TwoSidedIdeal.span S
  have hsub := hS.trans_subset (TwoSidedIdeal.subset_span (s := S))
  let q : MonoidAlgebra B G.G₀ →ₐ[B] I.ringCon.Quotient := RingCon.mkₐ B I.ringCon
  have hq : ∀ a b, q a = q b ↔ a - b ∈ I := fun a b =>
    (RingCon.eq _).trans (TwoSidedIdeal.rel_iff I a b)
  have hq0 : ∀ a ∈ I, q a = 0 := fun a ha => by
    rw [← map_zero q, hq, sub_zero]; exact ha
  let f : G.G₀ →* I.ringCon.Quotient := (q : _ →* _).comp (MonoidAlgebra.of B G.G₀)
  have hf : ∀ g, g ∈ f.ker ↔ MonoidAlgebra.single g 1 - 1 ∈ I := fun g => by
    rw [← hq, map_one]; rfl
  have hV : V.toSubgroup ≤ f.ker := fun g hg => (hf g).2 (hsub (Or.inr ⟨g, hg, rfl⟩))
  let U : OpenNormalSubgroup G.G₀ :=
    { toSubgroup := f.ker
      isOpen' := Subgroup.isOpen_mono hV V.isOpen
      isNormal' := MonoidHom.normal_ker f }
  refine (hf k).1 (pl_sub l G.Γ H G.η.ker G.η_open hH U (fun h hh => ?_) k hk)
  have hl : (l : B) ∈ maximalIdeal B := by
    have := hO.char
    rw [← res_eq_zero_iff O, map_natCast, CharP.cast_eq_zero]
  have hchi : (u.D.chi (MonoidAlgebra.single h 1)).map (res O B : B →+* ResidueField O) = (Polynomial.X - 1) ^ n := by
    rw [← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, u.red, MonoidAlgebra.mapRingHom_single, map_one]
    exact chi_diag _ _ (hχ h hh)
  obtain ⟨e, he⟩ := exists_prime_power_pow_eq_one l n N (maximalIdeal B)
    (fun a ha => by
      rw [← q.commutes]
      exact hq0 _ (hsub (Or.inl (Or.inr ⟨a, ha, rfl⟩)))) hl (q (MonoidAlgebra.single h 1))
    (u.D.chi (MonoidAlgebra.single h 1))
    (by
      rw [Polynomial.aeval_algHom_apply]
      exact hq0 _ (TwoSidedIdeal.span_le.2 (fun z hz => hsub (Or.inl (Or.inl (Or.inl hz)))) (ch_mem u.D _)))
    (fun i => by
      rw [← res_eq_zero_iff O]
      show (res O B : B →+* ResidueField O) _ = 0
      rw [← Polynomial.coeff_map, Polynomial.map_sub, hchi]
      simp)
  refine ⟨e, ?_⟩
  show f (h ^ l ^ e) = 1
  rw [map_pow]
  exact he
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.pl_map :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ') [H.Normal],
      IsOpen (H : Set Γ') → Continuous f → Function.Surjective f →
        (PL (l := l) (H.comap f)).map f = PL (l := l) H := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H _ _ hf hsurj
  have hmem {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {x : G} :
      x ∈ PL (l := l) K ↔
        ∀ U : OpenNormalSubgroup G, (∀ h ∈ K, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U := by
    simp only [PL, Subgroup.mem_iInf]
    rfl
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine hmem.mpr fun V hV => ?_
    let U : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap f hf
        isNormal' := Subgroup.Normal.comap V.isNormal' f }
    apply hmem.mp hx U
    intro h hh
    obtain ⟨e, he⟩ := hV (f h) hh
    refine ⟨e, ?_⟩
    change f (h ^ l ^ e) ∈ V
    rwa [map_pow]
  · intro y hy
    let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ U}
    let top : OpenNormalSubgroup Γ :=
      { toOpenSubgroup := ⊤
        isNormal' := Subgroup.normal_top }
    have htop : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ top := by
      intro h _
      exact ⟨0, Subgroup.mem_top _⟩
    have : Nonempty ι := ⟨⟨top, htop⟩⟩
    let t (i : ι) : Set Γ := f ⁻¹' {y} ∩ (i.1 : Set Γ)
    have hclosed (i : ι) : IsClosed (t i) :=
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (· ⊇ ·) t := by
      intro i j
      have hpow : ∀ h ∈ H.comap f, ∃ e : ℕ, h ^ l ^ e ∈ i.1 ⊓ j.1 := by
        intro h hh
        obtain ⟨a, ha⟩ := i.2 h hh
        obtain ⟨b, hb⟩ := j.2 h hh
        refine ⟨a + b, ⟨?_, ?_⟩⟩
        · rw [pow_add, pow_mul]
          exact pow_mem ha _
        · rw [add_comm, pow_add, pow_mul]
          exact pow_mem hb _
      exact ⟨⟨i.1 ⊓ j.1, hpow⟩, fun _ hx => ⟨hx.1, hx.2.1⟩, fun _ hx => ⟨hx.1, hx.2.2⟩⟩
    have hnonempty (i : ι) : (t i).Nonempty := by
      let V : OpenNormalSubgroup Γ' :=
        { toSubgroup := i.1.toSubgroup.map f
          isOpen' := f.isOpenMap_of_sigmaCompact hsurj hf _ i.1.toOpenSubgroup.isOpen
          isNormal' := Subgroup.Normal.map i.1.isNormal' f hsurj }
      have hyV : y ∈ V := by
        refine hmem.mp hy V fun h hh => ?_
        obtain ⟨x, rfl⟩ := hsurj h
        obtain ⟨e, he⟩ := i.2 x hh
        exact ⟨e, ⟨x ^ l ^ e, he, map_pow f x _⟩⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyV
      exact ⟨x, hxy, hx⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
      hnonempty (fun i => (hclosed i).isCompact) hclosed
    rw [Set.mem_iInter] at hx
    exact ⟨x, hmem.mpr fun U hU => (hx ⟨U, hU⟩).2, (hx ⟨top, htop⟩).1⟩
end

