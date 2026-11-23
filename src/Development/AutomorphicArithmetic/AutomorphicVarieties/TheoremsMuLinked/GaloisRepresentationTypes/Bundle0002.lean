module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RegDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.PolNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.OpOfProj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CoreOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl

private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)

theorem UpperTheory.V.Th.core_of :
    Th.OrdVan2 → W.PhiAll → Th.Core := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (l := l) (L := L) (Ω := Ω) (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 ((l : ℕ) : 𝓞 L)).1 (by simpa only [map_natCast] using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HasOp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Th.hasOp :
    HasOp := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b hb T Q
  refine ⟨2 * n.factorial, ?_⟩
  · skip
    intro N
    have hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal := by
      intro j hj
      apply Q.v_not N j
      left
      have h1 := (Q.B_w N j (l : 𝓞 L)).2 hj
      refine (Q.B_v N j (l : 𝓞 (Lp L))).1 ?_
      simpa using h1
    obtain ⟨A, ι, hι⟩ := hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N)
      (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)
    have hd := fun j => locData hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j)
      (Q.fr_frob N j) (Q.τ_gen N j)
    choose hq x δ hx hδ hrel using hd
    have hNq : T.Nq N = qj (Q.w N) := funext fun j => (Q.Nq N j).trans (hq j).symm
    have hok : LocOk A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j)) :=
      ⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩
    obtain ⟨A1, h1⟩ := opOfX hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok
      (fun j => by rw [← hNq]; exact T.Nq_mod N j)
    obtain ⟨A2, h2⟩ := opTransportX l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1
    have e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j)) := funext (Q.ph N)
    have e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j)) := funext (Q.ta N)
    rw [hNq, e1, e2]
    exact ⟨A2, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧
      (∀ s ∈ Dec (F := F) A, g⁻¹ * s * g ∈ Dec (F := F) B) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  have hD' : ∀ s ∈ Dec (F := F) (g • B), g⁻¹ * s * g ∈ Dec (F := F) B := fun s hs => by
    have h1 : s • g • B = g • B := hs
    show (g⁻¹ * s * g) • B = B
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  refine ⟨B, g, hB, hD', hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

private theorem flag_move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ (B : ValuationSubring Ω) (d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A)), IsPlaceOver B w ∧
      FlagAt M m (r.comp (res F Ω K)) B (fun i => (κ i).comp d) ∧
      (∀ s, cycBar F Ω l (d s) = cycBar K Ω l s) ∧
      (Dec (F := F) B ≤ (res F Ω K).range → Function.Surjective d) := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hκ⟩ := hκ
  obtain ⟨B, g, hB, hD', hD, hI⟩ := move w hA
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  refine ⟨B, d, hB, ⟨fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs,
    ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩, fun s => ?_, fun H s => ?_⟩
  · rw [MonoidHom.comp_apply, rep_conj]
    exact hP (d s)
  · have h := hκ i (d s) (hI s hs)
    rw [hd, char_conj, char_conj] at h
    exact h
  · rw [hd, char_conj]
    rfl
  · obtain ⟨t, ht⟩ := H (hD' s s.2)
    have htD : t ∈ Dec (F := K) B := by
      have h1 : res F Ω K t • B = B := by
        rw [ht]
        exact hD' s s.2
      exact h1
    refine ⟨⟨t, htD⟩, Subtype.ext ?_⟩
    rw [hd]
    show g * res F Ω K t * g⁻¹ = s
    rw [ht]
    group

end

theorem UpperTheory.V.Th.unlRes :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → ((∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range) → Unl l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) ∧ ((∀ i j, m i ≠ m j + 1) → Af.Level l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) := by
  intro K Ω _ _ _ _ _ _ _ l _ n M m r hM
  refine ⟨fun hdec H w hw => ?_, fun hm H w hw => ?_⟩
  · obtain ⟨A, hA, κ, hκ, hu⟩ := H (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, hc, hs⟩ := flag_move w hA hκ
    have hv : B.valuation (l : Ω) < 1 := by
      simpa only [map_natCast] using (hB (l : 𝓞 K)).2 hw
    refine ⟨B, hB, _, hF, fun i j e => hu i j (MonoidHom.ext fun s => ?_)⟩
    obtain ⟨t, rfl⟩ := hs (hdec B hv) s
    have h1 := DFunLike.congr_fun e t
    change κ i (d t) = κ j (d t) * cycBar K Ω l t at h1
    change κ i (d t) = κ j (d t) * cycBar ℚ Ω l (d t)
    rw [hc, h1]
  · obtain ⟨A, hA, κ, hκ⟩ := (Lev.LevelF.of_level H).above (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, -, -⟩ := flag_move w hA hκ
    exact ⟨B, hB, _, hF, Lev.unlGap K Ω l n M hM m _ w hw B hB _ hF hm⟩
end

