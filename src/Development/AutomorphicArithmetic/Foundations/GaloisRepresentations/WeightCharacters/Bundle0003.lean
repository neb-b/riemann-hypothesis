module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.Wt.famOf_of : ExpBasic → PevExp → SqExp → TopUp → WExp → FamOfA → FamOf := by
  intro hB hP hS hT hW hA E _ _ _ a τ C hC n hn W Q _ f hf P
  obtain ⟨hLe, hGe, hmono, -, hconst, -⟩ := hB
  obtain ⟨d₀, hd₀⟩ := hW E a τ W
  refine ⟨Finset.univ.sup (fun q => (P q).totalDegree) + d₀, fun ν X => ?_⟩
  have hsum : ∀ (T : Submodule ℂ (Circle → ℂ)) (F : Q → Circle → ℂ), (∀ q, F q ∈ T) → (fun z => ∑ q, F q z) ∈ T := by
    intro T F h
    have : (fun z => ∑ q, F q z) = ∑ q, F q := by funext z; simp [Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun q _ => h q
  refine ⟨(hA E a τ C hC n hn W ν Q f P X).1, ?_, ?_, ?_, ?_, ?_, (hA E a τ C hC n hn W ν Q f P X).2⟩
  · intro k hk y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.lev k hk]
    exact Finset.sum_congr rfl fun q _ => by rw [hf q k hk]
  · intro x y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.inf x x.2]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [(f q).2.2 x v, RU_apply, mul_assoc (n g), mul_assoc (n g)]
  · intro b hb y₁ y₂ v
    funext g
    rw [Pi.smul_apply, famOf_apply, famOf_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : delta ν (X q * (n g * (y₁ * b))) = chi ν b * delta ν (X q * (n g * y₁)) := by
      have e : X q * (n g * (y₁ * b)) = X q * (n g * y₁) * b := by simp only [mul_assoc]
      unfold delta
      rw [e, map_mul, Module.End.mul_apply, hT a ν b hb, map_smul, map_smul, smul_eq_mul]
    rw [this]; ring
  · intro k x hx y₁ y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).1
    have h2 : (fun z => delta ν (X q * (n g * (tor a k z * y₁)))) ∈ ExpLe (psum ν k) := by
      have := (hS a k ν (sqRep ℂ a ν y₁ (top ν)) ((ev1 ν) ∘ₗ (sqRep ℂ a ν (X q * n g)))).1
      refine (congrArg (· ∈ ExpLe (psum ν k)) (funext fun z => ?_)).mpr this
      rw [delta, LinearMap.comp_apply, ← mul_assoc (X q), map_mul (sqRep ℂ a ν) (X q * n g), map_mul (sqRep ℂ a ν) (tor a k z),
        Module.End.mul_apply, Module.End.mul_apply]
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).1
    refine (hmono _ _ ?_).1 (hLe _ _ _ _ (hLe _ _ _ _ h1 h2) h3)
    have : (P q).totalDegree ≤ Finset.univ.sup (fun q => (P q).totalDegree) :=
      Finset.le_sup (f := fun q => (P q).totalDegree) (Finset.mem_univ q)
    push_cast
    omega
  · intro k x hx y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).2
    have h2 := (hconst (delta ν (X q * (n g * 1)))).2
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).2
    refine (hmono _ _ ?_).2 (hGe _ _ _ _ (hGe _ _ _ _ h1 h2) h3)
    push_cast
    omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOffHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famOff_holds : FamOff := by
  intro E _ _ _ a τ W K ν d B hB U hU hBU hne τ' hτ'
  classical
  obtain ⟨y₁, y₂, v₀, hv₀⟩ := hne
  set v := InfinitePlace.mk τ' with hv
  obtain ⟨e, he⟩ : ∃ e, B y₁ y₂ (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 : B y₁ y₂ = 0 := by
      apply (Formalism.L2.DIV.bVV ℂ W).ext
      intro i
      have hi : Formalism.L2.DIV.bVV ℂ W i = GlobalTheory.CoefIrred.tenMul W
          (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (W τ) (i τ)) := by
        apply Subtype.ext
        rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe,
          Formalism.L2.DIV.bVVfun]
        simp only [GlobalTheory.CoefIrred.ssBasis_coe]
      rw [hi]
      exact hc _
    exact hv₀ (by rw [h1]; rfl)
  have h : (AU.mk ⟨U, hU⟩).HasWt v.embedding (W v) := by
    refine ⟨isIrreducible_sqRep a (W v), B y₁ y₂ ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun x => hBU _ _ _,
      fun x u => ?_⟩
    · have := LinearMap.congr_fun h0 (e v)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E a := embU_le_infU _ x.2
      have h1 : cEmb τ x.1 = 1 :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 τ) (by rw [InfinitePlace.mk_embedding]; exact hτ'.symm)
      have h2 := hB.inf ⟨x.1, hx⟩ y₁ y₂ (GlobalTheory.CoefIrred.tenMul W (Function.update e v u))
      rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2, h1, one_mul, one_mul] at h2
      exact h2.symm
  rcases InfinitePlace.embedding_mk_eq τ' with e | e
  · have h' := h
    rw [← Wt.at_embedding W v, e] at h'
    exact h'
  · have h2 := h.conjugate
    rw [← Wt.at_embedding W v, ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ'] at h2
    exact h2

theorem psum_succ {a : ℕ} (κ : DomWeight a) (i : Fin a) : psum κ (i + 1) = psum κ i + κ.w i := by
  have e : (Finset.univ.filter fun j : Fin a => j.val < i + 1) = insert i (Finset.univ.filter fun j : Fin a => j.val < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [psum, e, Finset.sum_insert (by simp), add_comm, psum]

theorem famWt_of : FamOff → FamSum → FamWt := by
  intro hOff hSum E _ _ _ a τ W K ν d B hB U hU hBU hne
  obtain ⟨mu, hmu⟩ := _root_.GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hU
  refine ⟨mu, ⟨hU, hmu, ?_⟩, fun τ' h => hasWeightAt_unique ⟨U, hU⟩ τ' (hmu τ') (hOff E a τ W K ν d B hB U hU hBU hne τ' h),
    fun i => ?_⟩
  · obtain ⟨y₁, y₂, v, hv⟩ := hne
    exact ⟨_, hBU y₁ y₂ v, hv, fun x hx => hB.fix x hx _ _ _⟩
  · have h1 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) i
    have h2 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) (i + 1)
    rw [psum_succ, psum_succ] at h2
    rw [abs_le]
    push_cast
    omega

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamProj
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famProj_of : EvLem → SumRep → FamProj := by
  intro hEv hSum E _ _ _ a τ W K ν d B hB
  classical
  obtain ⟨S₀, hS₀, hBS₀⟩ := hB.fin
  let S := S₀ ⊓ autU E a
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hBS : ∀ y₁ y₂ v, B y₁ y₂ v ∈ S := fun y₁ y₂ v => ⟨hBS₀ y₁ y₂ v, hB.aut y₁ y₂ v⟩
  obtain ⟨t, ht, hind, hle⟩ := hSum E a S inferInstance fun φ hφ => hφ.2
  have hex : ∀ U : Submodule ℂ (UA E a → ℂ), ∃ p : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ), U ∈ t → (∀ φ, p φ ∈ U) ∧
      (∀ φ ∈ U, p φ = φ) ∧ ∀ V ∈ t, V ≠ U → ∀ φ ∈ V, p φ = 0 := fun U => by
    by_cases hU : U ∈ t
    · obtain ⟨C, hC, hc⟩ := (hind (Finset.mem_coe.2 hU)).symm.exists_isCompl
      refine ⟨U.subtype ∘ₗ Submodule.projectionOnto U C hc.symm, fun _ => ⟨fun φ => Subtype.property _, fun φ hφ =>
        congrArg Subtype.val (Submodule.projectionOnto_apply_left hc.symm ⟨φ, hφ⟩), fun V hV hne φ hφ => ?_⟩⟩
      have h0 : Submodule.projectionOnto U C hc.symm φ = 0 :=
        Submodule.projectionOnto_apply_of_mem_right hc.symm
          (hC (le_sSup (show V ∈ (t : Set (Submodule ℂ (UA E a → ℂ))) \ {U} from ⟨hV, hne⟩) hφ))
      simp [h0]
    · exact ⟨0, fun h => absurd h hU⟩
  choose p hp using hex
  have key : ∀ φ ∈ S, ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ) := by
    let P : Submodule ℂ (UA E a → ℂ) :=
      { carrier := {φ | ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ)}
        add_mem' := fun h1 h2 => ⟨by simp only [map_add (f := _), Finset.sum_add_distrib, h1.1, h2.1], fun U hU x => by
          simp only [map_add (f := _), h1.2 U hU x, h2.2 U hU x]⟩
        zero_mem' := ⟨by simp, fun U _ x => by simp⟩
        smul_mem' := fun c φ h => ⟨by simp only [map_smul, ← Finset.smul_sum, h.1], fun U hU x => by
          simp only [map_smul, h.2 U hU x]⟩ }
    refine fun φ hφ => (sSup_le (a := P) fun V hV ψ hψ => ⟨?_, fun U hU x => ?_⟩) (hle hφ)
    · rw [Finset.sum_eq_single_of_mem V hV fun U hU hne => (hp U hU).2.2 V hV hne.symm ψ hψ]
      exact (hp V hV).2.1 ψ hψ
    · have hx := (ht V hV).stable x ψ hψ
      by_cases h : V = U
      · subst h
        rw [(hp V hV).2.1 _ hx, (hp V hV).2.1 _ hψ]
      · rw [(hp U hU).2.2 V hV h _ hx, (hp U hU).2.2 V hV h _ hψ, map_zero]
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ U g, (fun z => p U (Φ z) g) ∈ T := fun T Φ h1 h2 U g =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (LinearMap.proj g ∘ₗ p U ∘ₗ S.subtype)
  refine ⟨t, fun U y₁ y₂ => p U ∘ₗ B y₁ y₂, fun U hU => ⟨ht U hU, ⟨fun y₁ y₂ v => (ht U hU).aut _ ((hp U hU).1 _),
    fun k hk y₁ y₂ v => ?_, fun x y₁ y₂ v => ?_, fun b hb y₁ y₂ v => ?_, fun k x hx y₁ y₂ v g => ?_, fun k x hx y₂ v g => ?_,
    ⟨S.map (p U), inferInstance, fun y₁ y₂ v => ⟨_, hBS y₁ y₂ v, rfl⟩⟩⟩, fun y₁ y₂ v => (hp U hU).1 _⟩,
    fun y₁ y₂ v => (key _ (hBS y₁ y₂ v)).1⟩
  · show RU E a k (p U (B y₁ y₂ v)) = p U (B y₁ y₂ v)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.fix k hk]
  · show RU E a x (p U (B y₁ y₂ v)) = p U (B _ _ _)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.inf x]
  · show p U (B _ y₂ v) = chi ν b • p U (B y₁ y₂ v)
    rw [hB.up b hb, map_smul]
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hx y₁ y₂ v g) U g
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hx y₂ v g) U g

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamSum
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famSum_of : ExpBasic → EvLem → TorFacts → QR → WtBd → EmbProj → FamSum := by
  intro hEB hEv hTor hQR hBd hEP E _ _ _ a τ W K ν d B hB U hU hBU hne κ hκ k
  obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E a τ
  have hx : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = unitaryIncl a u := fun u => by
    have h := he (e.symm u)
    rw [e.apply_symm_apply] at h
    exact ⟨⟨(e.symm u).1, (Subgroup.mem_inf.1 (e.symm u).2).1⟩, (e.symm u).2, h.symm⟩
  choose x hx using fun z : Circle => (show ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = tor a k z by
    obtain ⟨u, hu⟩ := (hTor a k z).2.1
    rw [← hu]
    exact hx u)
  rename_i hxu
  have hc : IsCirc τ k x := hx
  obtain ⟨S, hS, hBS⟩ := hB.fin
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ L : (UA E a → ℂ) →ₗ[ℂ] ℂ, (fun z => L (Φ z)) ∈ T := fun T Φ h1 h2 L =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (L ∘ₗ S.subtype)
  obtain ⟨y₁, y₂, v, hv⟩ := hne
  constructor
  · obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU y₁ y₂ v) hv
    refine (hBd a k κ _).1 {w | ∃ y₁ y₂ v, w = p (B y₁ y₂ v)} ⟨_, ⟨y₁, y₂, v, rfl⟩, hp0⟩ ?_ ?_
    · rintro u _ ⟨y₁, y₂, v, rfl⟩
      obtain ⟨x', h1, h2⟩ := hxu u
      exact ⟨_, _, _, by rw [← h2, ← hp _ h1 _ (hBU _ _ _), hB.inf x']⟩
    · rintro _ ⟨y₁, y₂, v, rfl⟩ L
      have := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hc y₁ y₂ v g) (L ∘ₗ p)
      convert this using 2 with z
      rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z)]
      rfl
  · obtain ⟨y, v', hv'⟩ : ∃ y v', B 1 y v' ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨u, b, hb, rfl⟩ := hQR a y₁
      obtain ⟨x', -, h2⟩ := hxu u
      have e1 := hB.inf x' 1 ((cEmb τ x'.1)⁻¹ * y₂) (W.rep x'⁻¹ v)
      rw [h, map_zero, mul_one, mul_inv_cancel_left, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, h2] at e1
      rw [hB.up b hb, ← e1, smul_zero] at hv
      exact hv rfl
    obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU 1 y v') hv'
    refine (hBd a k κ _).2 _ hp0 fun L => ?_
    have h1 := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hc y v' g) (L ∘ₗ p)
    have h2 := hEB.2.1 _ _ _ _ (hEB.2.2.2.1 1 (psum ν k)).2 h1
    rw [sub_eq_add_neg]
    convert h2 using 2 with z
    rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z), (hx z).2, mul_one, ← one_mul (tor a k z),
      hB.up _ (hTor a k z).1, (hTor a k z).2.2.1, map_smul, map_smul, one_mul, one_mul]
    rfl

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplFin
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

namespace UpperTheory.Gal.Wt.KaplanskyFiniteness

variable {k : Type} [NormedField k] [IsUltrametricDist k]

private lemma norm_unit_le (c x : k) (hc : c ≠ 0) (h : ‖x‖ ≤ ‖c‖) : ‖1 - c⁻¹ * x‖ ≤ 1 := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
  rw [norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hc', mul_one]
  exact h

private lemma norm_le_of_near (c x : k) (h : ‖x - c‖ ≤ ‖c‖ / 2) : ‖x‖ ≤ ‖c‖ := by
  have hx : x = (x - c) + c := by ring
  rw [hx]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans ?_) le_rfl)
  have := norm_nonneg c
  linarith

private lemma pow_near {u : k} {ε : ℝ} (hε : 0 ≤ ε) (hu : ‖u‖ ≤ 1) (h : ‖u - 1‖ ≤ ε) (n : ℕ) :
    ‖u ^ n - 1‖ ≤ ε := by
  induction n with
  | zero => simpa using hε
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h)
    rw [norm_mul]
    calc ‖u‖ * ‖u ^ n - 1‖ ≤ 1 * ε := mul_le_mul hu ih (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

private lemma eval_bound (p : Polynomial k) (x : k) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖p.eval x‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * R ^ i := by
  rw [Polynomial.eval_eq_sum_range]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx i) (norm_nonneg _)

private lemma exists_pow_small (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ n : ℕ, M * (1 / 2 : ℝ) ^ n ≤ ε := by
  have hM1 : 0 < M + 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hM1) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc M * (1 / 2 : ℝ) ^ n ≤ (M + 1) * (1 / 2 : ℝ) ^ n := by nlinarith
    _ ≤ (M + 1) * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hn.le hM1.le
    _ = ε := by field_simp

end UpperTheory.Gal.Wt.KaplanskyFiniteness

open UpperTheory.Gal.Wt.KaplanskyFiniteness in
theorem UpperTheory.Gal.Wt.kaplFin_of :
    UpperTheory.Gal.Wt.KaplFin := by
  classical
  intro k _ _ s δ ε hδ hε hε1
  refine Finset.induction_on_max_value (fun c : k => ‖c‖) s ?_ ?_
  · intro _
    refine ⟨1, fun x _ => by simp, fun c hc => absurd hc (Finset.notMem_empty c), fun x _ => ?_⟩
    simpa using hε.le
  · intro c s _ hmax ih hs
    obtain ⟨p', h1, h2, h3⟩ := ih fun c' hc' => hs c' (Finset.mem_insert_of_mem hc')
    have hδc : δ ≤ ‖c‖ := hs c (Finset.mem_insert_self c s)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hδc
      linarith
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    obtain ⟨n, hn⟩ := exists_pow_small (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c‖ ^ i) ε
      (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) hε
    have hev : ∀ x, ((p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n).eval x) =
        p'.eval x * (1 - c⁻¹ * x) ^ n := by
      intro x
      simp [Polynomial.eval_mul, Polynomial.eval_pow]
    refine ⟨p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n, ?_, ?_, ?_⟩
    · intro x hx
      rw [hev, norm_mul, norm_pow]
      have hu := norm_unit_le c x hc0 (hx.trans hδc)
      calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ 1 * 1 :=
            mul_le_mul (h1 x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    · intro c' hc' x hx
      rw [hev, norm_mul, norm_pow]
      rcases Finset.mem_insert.mp hc' with rfl | hc's
      · have hxc := norm_le_of_near c' x hx
        have hu : ‖1 - c'⁻¹ * x‖ ≤ 1 / 2 := by
          have e : 1 - c'⁻¹ * x = c'⁻¹ * (c' - x) := by field_simp
          rw [e, norm_mul, norm_inv, norm_sub_rev, inv_mul_le_iff₀ hcpos]
          linarith
        calc ‖p'.eval x‖ * ‖1 - c'⁻¹ * x‖ ^ n
            ≤ (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c'‖ ^ i) * (1 / 2 : ℝ) ^ n :=
              mul_le_mul (eval_bound p' x _ hxc) (pow_le_pow_left₀ (norm_nonneg _) hu n)
                (by positivity) ((norm_nonneg _).trans (eval_bound p' x _ hxc))
          _ ≤ ε := hn
      · have hxc : ‖x‖ ≤ ‖c‖ := (norm_le_of_near c' x hx).trans (hmax c' hc's)
        have hu := norm_unit_le c x hc0 hxc
        calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ ε * 1 :=
              mul_le_mul (h2 c' hc's x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) hε.le
          _ = ε := mul_one ε
    · intro x hx
      have hxδ : ‖x‖ ≤ δ := hx.trans (by nlinarith)
      have hu := norm_unit_le c x hc0 (hxδ.trans hδc)
      have hu1 : ‖(1 - c⁻¹ * x) - 1‖ ≤ ε := by
        have e : (1 - c⁻¹ * x) - 1 = -(c⁻¹ * x) := by ring
        rw [e, norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos]
        calc ‖x‖ ≤ δ * ε := hx
          _ ≤ ‖c‖ * ε := mul_le_mul_of_nonneg_right hδc hε.le
      have hun := pow_near hε.le hu hu1 n
      have e : p'.eval x * (1 - c⁻¹ * x) ^ n - 1 =
          p'.eval x * ((1 - c⁻¹ * x) ^ n - 1) + (p'.eval x - 1) := by ring
      rw [hev, e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3 x hx))
      rw [norm_mul]
      calc ‖p'.eval x‖ * ‖(1 - c⁻¹ * x) ^ n - 1‖ ≤ 1 * ε :=
            mul_le_mul (h1 x hxδ) hun (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.kapl_of :
    UpperTheory.Gal.Wt.KaplFin → UpperTheory.Gal.Wt.Kapl := by
  intro hfin k _ _ Y hY δ ε hδ hε hε1
  have hY' : IsCompact (Y ∩ {x : k | δ ≤ ‖x‖}) :=
    hY.inter_right (isClosed_le continuous_const continuous_norm)
  have hnhds : ∀ c ∈ Y ∩ {x : k | δ ≤ ‖x‖}, Metric.closedBall c (‖c‖ / 2) ∈ nhds c := by
    intro c hc
    have hc' : δ ≤ ‖c‖ := hc.2
    exact Metric.closedBall_mem_nhds c (by linarith)
  obtain ⟨s, hs, hcov⟩ := hY'.elim_nhds_subcover (fun c => Metric.closedBall c (‖c‖ / 2)) hnhds
  obtain ⟨p, h1, h2, h3⟩ := hfin k s δ ε hδ hε hε1 (fun c hc => (hs c hc).2)
  have hbig : ∀ x ∈ Y, δ ≤ ‖x‖ → ‖p.eval x‖ ≤ ε := by
    intro x hx hxδ
    have hmem := hcov ⟨hx, hxδ⟩
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨c, hc, hxc⟩ := hmem
    exact h2 c hc x (by simpa [dist_eq_norm] using hxc)
  refine ⟨p, fun x hx => ?_, hbig, h3⟩
  rcases le_total ‖x‖ δ with h | h
  · exact h1 x h
  · exact (hbig x hx h).trans hε1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NrmAut
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.nrmAut_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.NrmAut := by
  intro hC E _ _ _ a τ C hCl n hn p hp
  obtain ⟨hpc, A, hAf, hA⟩ := hp
  let S : Submodule ℂ (UA E a → ℂ) := A.map (LinearMap.funLeft ℂ ℂ n)
  have hSf : FiniteDimensional ℂ S := inferInstance
  have hS : ∀ y, (fun g => p (n g * y)) ∈ S := fun y => ⟨_, hA y, rfl⟩
  refine ⟨fun y => ?_, S, hSf, hS⟩
  refine hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g])
    (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)
  · have he : (fun x : infU E a => p (n (g * x.1) * y)) =
        fun x : infU E a => p (n g * (cEmb τ x.1 * y)) := by
      funext x
      rw [hn.inf x.1 x.2 g, mul_assoc]
    rw [he]
    exact hpc.comp (continuous_const.mul
      (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))
  · have he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y)) := by
      funext g
      change p (n (g * x) * y) = _
      rw [hn.inf x hx g, mul_assoc]
    rw [he]
    exact hS _
end

