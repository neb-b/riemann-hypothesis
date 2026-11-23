module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
public import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtApart
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pAtApart :
    JEq → AtApart := by
  intro hJ
  unfold AtApart
  intro E _ _ _ A n p _ S T hc w hw hp
  have key : ∀ (u : Plc E) (hu : IsSplitAt u) (hpu : (p : 𝓞 E) ∉ u.asIdeal)
      (x : GL (Fin n) (u.adicCompletion E)),
      T.sec ((T.at hc u hu hpu).loc x) = UpperTheory.Gal.CertificateRingHomMap.loc hu x := by
    intro u hu hpu x
    apply (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
    intro v
    by_cases hv : (p : 𝓞 E) ∈ v.asIdeal
    · rw [T.sec_p _ v hv, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hu (apart_of_not_mem hpu hv)]
    · exact (T.j_eq _ _).1 (T.j_sec _) v hv
  refine ⟨key w hw hp, ?_⟩
  intro w' hw' hp' hap
  constructor
  · intro x
    show comp w (T.sec ((T.at hc w' hw' hp').loc x)) = 1
    rw [key w' hw' hp' x]
    exact UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw' hap x
  · intro x
    show comp w' (T.sec ((T.at hc w hw hp).loc x)) = 1
    rw [key w hw hp x]
    exact UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw (Ne.symm hap) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHasEigOf
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

private theorem hAct_slice {X V : Type} [Group X] [AddCommGroup V] [Module ℂ V] (K : Subgroup X)
    (hK : IsCommensurated K) (f : X → ℂ) (hf : f ∈ Hecke ℂ K) (φ : X → V) (L : V →ₗ[ℂ] V) (a g : X) :
    hAct K f (fun x => L (φ (a * x))) g = L (hAct K f φ (a * g)) := by
  have hfin := Formalism.UG.P.finite_supp K hK f hf
  unfold hAct
  rw [map_finsum L (hfin.subset (fun x hx => by
    intro h0; apply hx; simp [h0]))]
  refine finsum_congr fun x => ?_
  rw [map_smul, mul_assoc]

private theorem op_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {V : Type} [AddCommGroup V] [Module ℂ V]
    (K : Subgroup G.GAf) (f : G.GAf → ℂ) (F : G.GAf × Gr G 1 → V) (g : G.GAf) (g₂ : Gr G 1) :
    UpperTheory.Gal.Spc.op K f F (g, g₂) = hAct K f (fun x => F (x, g₂)) g := by
  unfold UpperTheory.Gal.Spc.op hAct
  refine finsum_congr fun h => ?_
  simp [Prod.mk_mul_mk]

private theorem op_eig {p : ℕ} [Fact p.Prime] {G : HTGroup p} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
    (ι : Γ →* G.GAf × Gr G 1) (K : Subgroup G.GAf) (hK : IsCommensurated K) (ξ' : Representation ℂ Γ V)
    (φ : G.GAf → V) (F : G.GAf × Gr G 1 → V)
    (hF : ∀ g₂ : Gr G 1, (∀ g, F (g, g₂) = 0) ∨ ∃ γ, ∀ g, F (g, g₂) = ξ' γ (φ ((ι γ).1⁻¹ * g)))
    (f : G.GAf → ℂ) (hf : f ∈ Hecke ℂ K) (c : ℂ) (h : hAct K f φ = c • φ) :
    UpperTheory.Gal.Spc.op K f F = c • F := by
  funext ⟨g, g₂⟩
  rw [op_eq]
  rcases hF g₂ with h0 | ⟨γ, hγ⟩
  · have e : (fun x => F (x, g₂)) = fun _ => 0 := funext h0
    rw [e]
    simp [hAct, h0]
  · have e : (fun x => F (x, g₂)) = fun x => ξ' γ (φ ((ι γ).1⁻¹ * x)) := funext hγ
    rw [e, hAct_slice K hK f hf, h]
    simp [hγ]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pHasEigOf :
    StdForm → PInt → PPart → ExtP → HasEigOf := by
  intro hStd hPI hPP hExt E _ _ _ A n p _ S T V _ _ ξ Φ hΦL hΦR hΦ0 K₀ hK₀ hK₀inv J ψ θ e hψ he heΦ hψΦ
  obtain ⟨B, x, hx, ee, hee, hemb⟩ := hStd E A n p S T
  let ξ' : Representation ℂ (S.G.Cˣ × ℚˣ) V := ξ
  let ξ₀ : Representation ℂ (GlobalTheory.LKCx.grp S.G B.β) V := ξ'.comp (GlobalTheory.LKCx.grp S.G B.β).subtype
  let φ : S.G.GAf → V := fun h => Φ (T.sec h)
  have hEq : ∀ γ : GlobalTheory.LKCx.grp S.G B.β, (B.embAt x 1 hx γ).2 ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G → ∀ g,
      φ ((B.embAt x 1 hx γ).1 * g) = ξ₀ γ (φ g) := by
    intro γ hγ g
    have h1 : (B.embAt x 1 hx γ).1 = T.j (rat (ee γ)) := hemb γ
    have hy : inclG S.G 1 (locC S.G ((ee γ : Gam0 E n) : GL (Fin n) E × ℚˣ)) ∈ UpperTheory.Gal.LocalSmoothExtension.Kp S.G := by
      rw [hee]; exact hγ
    obtain ⟨hI, -⟩ := hPI E A n p S (ee γ) hy
    obtain ⟨k, hk, hk1, hk2, hk3⟩ := hPP E A n p S T (rat (ee γ))
    have hsec : T.sec (T.j (rat (ee γ))) = rat (ee γ) * k⁻¹ := eq_mul_inv_of_mul_eq hk.symm
    have hc : k⁻¹ * T.sec g = T.sec g * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hk3 g, inv_mul_cancel_left]
    have hR : ∀ g', Φ (g' * k⁻¹) = Φ g' := hΦR k⁻¹
      (fun w hw => by rw [map_inv, hk1 w hw, inv_one])
      (fun w hw => by rw [map_inv]; exact inv_mem (by rw [hk2 w hw]; exact hI w hw))
    show Φ (T.sec ((B.embAt x 1 hx γ).1 * g)) = ξ₀ γ (Φ (T.sec g))
    rw [h1, map_mul, hsec, mul_assoc, hc, hΦL, hR, hee]
    rfl
  obtain ⟨F, hF1, hF2⟩ := hExt (GlobalTheory.LKCx.grp S.G B.β) S.G.GAf (Gr S.G 1) V (B.embAt x 1 hx) K₀
    (UpperTheory.Gal.LocalSmoothExtension.Kp S.G) ξ₀ φ hEq (fun k hk g => hK₀inv k hk g)
  have hne : F ≠ 0 := by
    obtain ⟨g₀, hg₀, hg₀p⟩ := hΦ0
    obtain ⟨k, hk, hk1, hk2, -⟩ := hPP E A n p S T g₀
    have h2 : Φ g₀ = φ (T.j g₀) := by
      calc Φ g₀ = Φ (T.sec (T.j g₀) * k) := congrArg Φ hk
        _ = φ (T.j g₀) := hΦR k hk1 (fun w hw => by rw [hk2 w hw]; exact hg₀p w hw) _
    intro h0
    apply hg₀
    rw [h2, ← hF1, h0]
    rfl
  refine ⟨B, x, 1, hx, (F : S.G.GAf × Gr S.G 1 → V), F.2, ?_, ?_, fun j => ?_⟩
  · intro h0
    exact hne (Subtype.ext h0)
  · have := op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 e he 1 (by simpa using heΦ)
    simpa using this
  · exact op_eig (B.embAt x 1 hx) K₀ hK₀ ξ₀ φ (F : S.G.GAf × Gr S.G 1 → V) hF2 (ψ j) (hψ j) (θ j) (hψΦ j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntConj
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem rel_at {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (UpperTheory.Gal.CertificateRingHomMap.cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem val_le_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (k : GUf E n)
    (hk : ∀ u : Plc E, comp u k ∈ GlobalTheory.LFun.KGL u (n := n)) (u : Plc E) :
    Valued.v (pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ))) ≤ 1 := by
  have h := congrFun (congrFun (rel_at k u) ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.transpose_apply, Matrix.map_apply] at h
  rw [← h]
  have hG := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val (UpperTheory.Gal.CertificateRingHomMap.cj u) _).1 (hk _)
  have ha := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).1 (hk u)
  rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
  refine sum_mem fun j _ => mul_mem ?_ ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [(conjLoc_spec (GlobalTheory.SplitPts.conjE E) u).2.2]
    exact hG.1 j ⟨0, hn⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ha.1 j ⟨0, hn⟩

private theorem exists_over {E : Type} [Field E] [NumberField E] (v : Plc ℚ) :
    ∃ w : Plc E, GroundTheory.Global.AdeleBaseChange.below ℚ w = v := by
  haveI := v.isMaximal
  obtain ⟨P, hP, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
    (GroundTheory.Global.AdeleBaseChange.below_eq_iff _ _).2 hlo⟩

private theorem sim_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (g : GUf E n)
    (hg : ∀ u : Plc E, comp u g ∈ GlobalTheory.LFun.KGL u (n := n)) : sim g ∈ ZU := by
  intro v
  obtain ⟨w, rfl⟩ := exists_over (E := E) v
  have h1 := val_le_one hn g hg w
  have h2 := val_le_one hn g⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hg u)) w
  have hmul : pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ)) *
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ)) = 1 := by
    rw [← map_mul, ← map_mul, map_inv, Units.mul_inv, map_one, map_one]
  have hv := congrArg Valued.v hmul
  rw [map_mul, map_one] at hv
  have h3 : Valued.v (pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ))) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : _) = _ := hv.symm
      _ ≤ Valued.v (pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  have h4 : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) = 1 := h3
  rw [GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply, GroundTheory.Global.SemiLocal.valued_completionMap] at h4
  have he : w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 0 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (GroundTheory.Global.AdeleBaseChange.below ℚ w).asIdeal w.asIdeal
      (GroundTheory.Global.AdeleBaseChange.below ℚ w).ne_bot]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal
      (GroundTheory.Global.AdeleBaseChange.below ℚ w).ne_bot
  exact (pow_eq_one_iff.1 h4).resolve_right he

private theorem finite_bad {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (g : GUf E n) :
    {u : Plc E | comp u g ∉ GlobalTheory.LFun.KGL u (n := n)}.Finite := by
  have hx : ∀ x : GlobalTheory.CuspRep.Af E, ∀ᶠ u : Plc E in Filter.cofinite, Valued.v (pLoc E u x) ≤ 1 := fun x => x.2
  have h1 : ∀ᶠ u : Plc E in Filter.cofinite, ∀ i j, Valued.v (pLoc E u ((mat g).val i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hx _
  have h2 : ∀ᶠ u : Plc E in Filter.cofinite, ∀ i j, Valued.v (pLoc E u ((mat g⁻¹).val i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hx _
  have h3 : ∀ᶠ u : Plc E in Filter.cofinite, comp u g ∈ GlobalTheory.LFun.KGL u (n := n) := by
    filter_upwards [h1, h2] with u a b
    refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨a, ?_⟩
    rw [← map_inv]
    exact b
  exact Filter.eventually_cofinite.1 h3

theorem UpperTheory.Gal.W2.Seed.pIntConj :
    IntConj := by
  intro E _ _ _ n g w hn
  exact ⟨fun hs hw => UpperTheory.Gal.CertificateRingHomMap.pIntConj_of E n g w hs hw, sim_unit hn g, finite_bad g⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIdx
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem relIndex_ne_zero_of_isOpen {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K O : Subgroup X} (hK : IsCompact (K : Set X)) (hO : IsOpen (O : Set X)) : O.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((O.subgroupOf K : Subgroup K) : Set K) := hO.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'

private theorem isOpen_map_conj {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    {K : Subgroup X} (hK : IsOpen (K : Set X)) (g : X) :
    IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  have e : ((K.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) =
      (fun x => g⁻¹ * x * g) ⁻¹' (K : Set X) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  rw [e]
  exact hK.preimage (by fun_prop)

theorem UpperTheory.Gal.W2.Seed.pKNIdx :
    KNOpen → KNIdx := by
  intro hop E _ _ _ A n p _ S T N hN
  obtain ⟨Lv, hLv⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N hN
  have hKo : IsOpen (S.L.KN N : Set S.G.GAf) := hLv ▸ Lv.K.isOpen
  have hKc : IsCompact (S.L.KN N : Set S.G.GAf) := hLv ▸ Lv.compact
  refine ⟨fun g => relIndex_ne_zero_of_isOpen hKc (isOpen_map_conj hKo g), fun K hKc' _ h0 => ?_⟩
  have hO := relIndex_ne_zero_of_isOpen hKc' (hop E A n p S T N hN)
  have e : S.L.KN N = ((S.L.KN N).comap T.j).comap T.sec := by
    ext h
    simp [Subgroup.mem_comap, T.j_sec]
  rw [e, Tr.lv, Subgroup.relIndex_comap] at h0
  exact hO (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNOpen
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

private def sg {E : Type} [Field E] [NumberField E] (U : Set (Plc E)) (N : ℕ) : AddSubgroup (Af E) where
  carrier := {x | ∀ w ∈ U, Valued.v (pLoc E w x) ≤ Valued.v (N : w.adicCompletion E)}
  zero_mem' := fun w _ => by simp
  add_mem' := fun {a b} ha hb w hw => by
    rw [map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le (ha w hw) (hb w hw))
  neg_mem' := fun {a} ha w hw => by
    rw [map_neg, Valuation.map_neg]
    exact ha w hw

private theorem isOpen_sg_univ {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 0 < N) :
    IsOpen (sg (E := E) Set.univ N : Set (Af E)) := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨c, hc⟩ : ∃ c : Af E, c * (N : Af E) = 1 := by
    refine ⟨algebraMap E (Af E) ((N : E)⁻¹), ?_⟩
    have h : algebraMap E (Af E) ((N : E)⁻¹) * algebraMap E (Af E) (N : E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hNE, map_one]
    simpa using h
  have hv : ∀ w : Plc E, Valued.v (pLoc E w c) * Valued.v (N : w.adicCompletion E) = 1 := fun w => by
    have h := congrArg (pLoc E w) hc
    rw [map_mul, map_natCast, map_one] at h
    rw [← map_mul, h, map_one]
  have h1 : IsOpen {f : Af E | ∀ w : Plc E, (f w : w.adicCompletion E) ∈
      ((Valued.v.integer : Subring (w.adicCompletion E)) : Set (w.adicCompletion E))} :=
    RestrictedProduct.isOpen_forall_mem (fun w => Valued.isOpen_integer _)
  have h2 : Continuous (fun x : Af E => c * x) := continuous_const.mul continuous_id
  have h3 := h1.preimage h2
  convert h3 using 1
  ext x
  have hm : ∀ w : Plc E, (((c * x : Af E) w : w.adicCompletion E) ∈
      ((Valued.v.integer : Subring (w.adicCompletion E)) : Set (w.adicCompletion E))) ↔
      Valued.v (pLoc E w c) * Valued.v (pLoc E w x) ≤ 1 := fun w => by
    rw [← map_mul, ← map_mul]
    exact Valuation.mem_integer_iff _ _
  constructor
  · intro hx w
    refine (hm w).2 ?_
    calc Valued.v (pLoc E w c) * Valued.v (pLoc E w x)
        ≤ Valued.v (pLoc E w c) * Valued.v (N : w.adicCompletion E) := by
          gcongr
          exact hx w trivial
      _ = 1 := hv w
  · intro hx w _
    have h := (hm w).1 (hx w)
    calc Valued.v (pLoc E w x)
        = Valued.v (pLoc E w c) * Valued.v (pLoc E w x) * Valued.v (N : w.adicCompletion E) := by
          rw [mul_right_comm, hv, one_mul]
      _ ≤ 1 * Valued.v (N : w.adicCompletion E) := by gcongr
      _ = _ := one_mul _

private theorem principalCongruence_map_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (w : Plc E)
    (M : GL (Fin n) (Af E)) :
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) M) ↔
      ∀ i k, Valued.v (pLoc E w ((M.val - 1) i k)) ≤ Valued.v (N : w.adicCompletion E) := by
  have h : ∀ i k, ((GeneralLinearGroup.map (pLoc E w) M).val - 1) i k = pLoc E w ((M.val - 1) i k) := by
    intro i k
    by_cases hik : i = k <;> simp [Matrix.sub_apply, Matrix.one_apply, hik]
  simp only [Cong1, h]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pKNOpen :
    KNIff → KNOpen := by
  intro hI E _ _ _ A n p _ S T N hN
  have hO : IsOpen ((sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : AddSubgroup (Af E)) : Set (Af E)) :=
    AddSubgroup.isOpen_mono (H₁ := sg Set.univ N) (fun x hx w _ => hx w trivial) (isOpen_sg_univ hN)
  have hm : Continuous (fun g : GUf E n => mat g) := continuous_fst.comp continuous_subtype_val
  have hc1 : Continuous (fun g : GUf E n => (T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val) :=
    Units.continuous_val.comp ((continuous_const.mul hm).mul continuous_const)
  have hc2 : Continuous (fun g : GUf E n => (T.a * mat g⁻¹ * T.a⁻¹ : GL (Fin n) (Af E)).val) := by
    simp only [map_inv]
    exact Units.continuous_val.comp ((continuous_const.mul hm.inv).mul continuous_const)
  have key : (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n)) =
      ⋂ (i : Fin n) (k : Fin n),
        ((fun g : GUf E n => ((T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val - 1) i k) ⁻¹'
            (sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : Set (Af E)) ∩
         (fun g : GUf E n => ((T.a * mat g⁻¹ * T.a⁻¹ : GL (Fin n) (Af E)).val - 1) i k) ⁻¹'
            (sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : Set (Af E))) := by
    ext g
    have e1 := (hI E A n p S T g).2 N hN
    have e2 := (hI E A n p S T g⁻¹).2 N hN
    rw [map_inv] at e2
    have hmem : g ∈ (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n)) ↔
        S.L.CongOne N (T.j g) ∧ S.L.CongOne N (T.j g)⁻¹ := Iff.rfl
    rw [hmem, e1, e2]
    simp only [principalCongruence_map_iff, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩ i k
      exact ⟨fun w hw => h1 w hw i k, fun w hw => h2 w hw i k⟩
    · intro h
      exact ⟨fun w hw i k => (h i k).1 w hw, fun w hw i k => (h i k).2 w hw⟩
  rw [key]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_
  · exact hO.preimage ((hc1.matrix_elem i k).sub continuous_const)
  · exact hO.preimage ((hc2.matrix_elem i k).sub continuous_const)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevFact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem apart_or {E : Type} [Field E] [NumberField E] [IsCMField E] (u w : Plc E) :
    GlobalTheory.Cong.Apart u w ∨ u = w ∨ u = UpperTheory.Gal.CertificateRingHomMap.cj w := by
  by_cases h : GlobalTheory.Cong.Apart u w
  · exact Or.inl h
  · exact Or.inr (GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (not_not.1 h))

private theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    UpperTheory.Gal.CertificateRingHomMap.cj (UpperTheory.Gal.CertificateRingHomMap.cj w) = w := GlobalTheory.CompanionTheory.OnlyStab.conjSrc_invol w

theorem UpperTheory.Gal.W2.Seed.pLevFact :
    AtApart → IntConj → LevFact := by
  intro hA hI E _ _ _ A n p _ S T hc S₀ Kw w hw hp hcj
  have hsec : ∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x := (hA E A n p S T hc w hw hp).1
  have hn : 0 < n := S.facts.pos
  refine ⟨fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩, fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hwS hu
      · subst h; exact absurd (by rwa [cj_cj]) hcu
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.1 w hwS
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hu hwS
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h
        refine (hI E n (CertificateRingHomMap.loc hw x) w hn).1 ?_ ?_
        · rw [CertificateRingHomMap.sim_loc]; exact one_mem _
        · rw [CertificateRingHomMap.comp_loc]; exact hx
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.2 w hwS hcj
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemAct
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemAct :
    MemSum → SumDoset → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → MemAct := by
  intro hMS hSD hTF hS X M M' _ _ _ T L' Kw hfT hap K KM htr hfK hK0 hKM hidx hnor t z h hz hh hc
  have hKMK : KM ≤ K := hKM.trans hK0
  have hcK : ∀ u ∈ KM, h * u * h⁻¹ ∈ K := fun u hu => hK0 (by simpa using hc 1 K.one_mem u hu)
  obtain ⟨hmem, -, hsum⟩ := hMS X K KM T.K₀ h hK0 hidx hnor hc
  refine ⟨hmem, ?_, ?_⟩
  · rw [map_mul, hap.1 t, hz.2, one_mul]
  · intro V _ _ Φ hΦ
    have hΦK : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g := by
      intro k hk g
      rw [hΦ k (htr.1 hk) g, htr.2 k hk, Units.val_one, one_smul]
    have hΦ0 : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g := fun k hk g => hΦK k (hK0 hk) g
    funext g
    rw [Pi.smul_apply, hsum V Φ hΦ0 g, hSD X K KM h hKMK hidx hcK V Φ hΦK hnor g,
      hTF X M M' T L' Kw hfT hap t z hz V Φ hΦ g]
    congr 1
    refine Eq.trans ?_ (hS X M' L' K Kw hfK t V (fun y => Φ (g * z * y)) ?_)
    · show ∑ᶠ x : X ⧸ K, dosetInd ℂ K h⁻¹ x.out • Φ (g * x.out) =
        ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Φ (g * z * y.out)
      rw [hh, ← finsum_comp_equiv (MulAction.toPerm z : Equiv.Perm (X ⧸ K))]
      refine finsum_congr fun q => ?_
      have hzq : (MulAction.toPerm z q : X ⧸ K) = ((z * q.out : X) : X ⧸ K) := by
        rw [MulAction.toPerm_apply]
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (z * q.out)
      have e1 : Φ (g * (z * q.out * k)) = Φ (g * z * q.out) := by
        rw [← mul_assoc, hΦK _ k.2, ← mul_assoc]
      have hmem2 : z * q.out * k ∈ DoubleCoset.doubleCoset (L'.loc t * z) (K : Set X) K ↔
          q.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
        simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
        constructor
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * (k : X)⁻¹, K.mul_mem hb (K.inv_mem k.2), ?_⟩
          have hw : a * (L'.loc t * z) * b = z * (a * L'.loc t * b) := by
            rw [← mul_assoc a, ← hz.1, mul_assoc z]
          calc q.out = z⁻¹ * (z * q.out * k) * (k : X)⁻¹ := by group
            _ = z⁻¹ * (z * (a * L'.loc t * b)) * (k : X)⁻¹ := by rw [e, hw]
            _ = a * L'.loc t * (b * (k : X)⁻¹) := by group
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * k, K.mul_mem hb k.2, ?_⟩
          rw [e, ← mul_assoc a, ← hz.1]
          group
      have e2 : dosetInd ℂ K (L'.loc t * z) (z * q.out * k) = dosetInd ℂ K (L'.loc t) q.out := by
        unfold dosetInd
        simp only [Set.indicator_apply, hmem2, Pi.one_apply]
      rw [hzq, hk, e1, e2]
    · intro k hk y
      show Φ (g * z * (y * k)) = Φ (g * z * y)
      rw [← mul_assoc]
      exact hΦK k hk _
end

