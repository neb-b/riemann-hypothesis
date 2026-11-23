module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.CharShape
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.TrTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.TwoUnder
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exSec {W P : Type} {X : P → Type} (f : W → P) (S : Set W) (inj : Set.InjOn f S)
    (g : ∀ w, w ∈ S → X (f w)) (d : ∀ p, X p) : ∃ b : ∀ p, X p, ∀ w (h : w ∈ S), b (f w) = g w h := by
  classical
  refine ⟨fun p => if h : ∃ w, ∃ hw : w ∈ S, f w = p then h.choose_spec.choose_spec ▸ g _ h.choose_spec.choose else d p, ?_⟩
  intro w hw
  have key : ∀ (w' : W) (hw' : w' ∈ S) (he : f w' = f w), (he ▸ g w' hw' : X (f w)) = g w hw := by
    intro w' hw' he
    obtain rfl := inj hw' hw he
    rfl
  have hex : ∃ w', ∃ hw' : w' ∈ S, f w' = f w := ⟨w, hw, rfl⟩
  simp only [dif_pos hex]
  exact key _ _ _

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem exOver (v : Pl (Lp L)) : ∃ w : Plc L, un w = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hne : P ≠ ⊥ := fun h => v.ne_bot (by
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 (Lp L)) (𝓞 L)))
  exact ⟨⟨P, hPm.isPrime, hne⟩, HeightOneSpectrum.ext (by
    rw [HeightOneSpectrum.under_asIdeal]
    exact hP.over.symm)⟩

private theorem exTwo : ∃ w : Plc L, (2 : 𝓞 L) ∈ w.asIdeal := by
  have hu : ¬ IsUnit (2 : 𝓞 L) := fun h => by
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ((u : 𝓞 L) : L) = algebraMap ℚ L (1 / 2) := by
      have e1 : (2 : L) * ((u : 𝓞 L) : L) = 1 := by
        have := congrArg (algebraMap (𝓞 L) L) hu
        rwa [map_mul, map_ofNat, map_one] at this
      rw [map_div₀, map_one, map_ofNat]
      field_simp
      linear_combination e1
    have hi : IsIntegral ℤ (algebraMap ℚ L (1 / 2)) := e ▸ u.2
    have hi' : IsIntegral ℤ (1 / 2 : ℚ) := (isIntegral_algebraMap_iff ).1 hi
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
    have h2 : (2 : ℚ) * (y : ℚ) = 1 := by
      rw [show (y : ℚ) = 1 / 2 from hy]; norm_num
    have h3 : (2 : ℤ) * y = 1 := by exact_mod_cast h2
    omega
  obtain ⟨P, hPm, hP⟩ := exists_max_ideal_of_mem_nonunits hu
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hP
    exact two_ne_zero hP
  exact ⟨⟨P, hPm.isPrime, hne⟩, hP⟩

private theorem two_under (w : Plc L) (h : (2 : 𝓞 (Lp L)) ∈ (un w).asIdeal) : (2 : 𝓞 L) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_ofNat] at h
  exact h

private def pullLev {B : Bridge L} {w : Plc L} (T : B.toRingBr.Split w) (V : Lev (Kw w)) : Lev (Kv (un w)) where
  c := V.c
  H := V.H.comap (Units.map (T.i : Kv (un w) →* Kw w))
  le := fun x hx => V.le ((T.Uc _ x).2 hx)
  H_le := fun x hx => (T.Uo x).1 (V.H_le hx)

theorem UpperTheory.V.Z.Sym.So.fitEx :
    UpperTheory.V.Z.Sym.So.FitEx := by
  classical
  intro L _ _ _ B hB T S VL hP h2
  have hinj : Set.InjOn (fun w : Plc L => un w) (S : Set (Plc L)) := hP.inj
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨sf, hsf⟩ := exSec (X := fun v : Pl (Lp L) => Kv v) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => (T w (hP.split w hw)).s) (fun _ => 0)
    obtain ⟨Vf, hVf⟩ := exSec (X := fun v : Pl (Lp L) => Lev (Kv v)) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => pullLev (T w (hP.split w hw)) (VL w)) (fun _ => Lev.iw _)
    obtain ⟨χ, hχ⟩ := hB.chi
    have hs : ∀ v ∈ S.image (fun w : Plc L => un w), sf v * sf v = cv v B.Δ := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      rw [hsf w hw]
      exact (T w (hP.split w hw)).hs
    let A : SD B.Δ :=
      { Sg := S.image (fun w : Plc L => un w)
        s := sf
        hs := hs
        V := Vf
        Ry := fun v => (finFacts _ (Vf v)).2.2.2.2.1.choose
        χ := χ }
    have hoff : ∀ v ∉ A.Sg, (2 : 𝓞 (Lp L)) ∉ v.asIdeal := by
      intro v hv h
      obtain ⟨w, rfl⟩ := exOver v
      obtain ⟨w', hw', he⟩ := h2 w (two_under w h)
      exact hv (Finset.mem_image.2 ⟨w', hw', he⟩)
    refine ⟨A, ⟨inferInstance, B.neg, ?_, ?_, ?_, ?_⟩, ⟨hP, ?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨w, hw⟩ := exTwo (L := L)
      obtain ⟨w', hw', -⟩ := h2 w hw
      exact ⟨_, Finset.mem_image_of_mem _ hw'⟩
    · exact fun v hv => B.loc v (hoff v hv)
    · intro v
      by_cases hv : v ∈ A.Sg
      · exact hχ v (Or.inr ⟨sf v, (hs v hv).symm⟩)
      · exact hχ v (Or.inl (hoff v hv))
    · exact fun v _ => (finFacts _ (Vf v)).2.2.2.2.1.choose_spec
    · intro v
      simp [A]
    · intro w hw h
      exact hsf w hw
    · intro w hw
      show (Vf (un w)).c = _
      rw [hVf w hw]; rfl
    · intro w hw h x
      show _ ↔ x ∈ (Vf (un w)).H
      rw [hVf w hw]; rfl
  · obtain ⟨b, hb⟩ := exSec (X := fun v : Pl (Lp L) => (Kv v)ˣ →* ℂˣ) (fun w : Plc L => un w) (S : Set (Plc L)) hinj
      (fun w hw => (a w).comp (iu T w (hP.split w hw))) (fun _ => 1)
    exact ⟨b, fun w hw h => hb w hw⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ValInvAnti
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Dominance

variable {k : Type} [Field k] [ValuativeRel k]

private theorem dom_three {x y z : kˣ} (h1 : valuation k (x : k) ≤ valuation k (y : k))
    (h2 : valuation k (y : k) ≤ valuation k (z : k)) : Dom ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> first | exact h1 | exact h2 | exact h1.trans h2

private theorem val_inv_anti {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) :
    valuation k ((y⁻¹ : kˣ) : k) ≤ valuation k ((x⁻¹ : kˣ) : k) := by
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀]
  exact inv_anti₀ ((Valuation.pos_iff _).2 x.ne_zero) h

private theorem dom_rev {d : Fin 3 → kˣ} (h : Dom d) : Dom ![(d 2)⁻¹, (d 1)⁻¹, (d 0)⁻¹] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> first | exact le_rfl | exact val_inv_anti (h _ _ (by decide))

private theorem dom_mul {n : ℕ} {a b : Fin n → kˣ} (ha : Dom a) (hb : Dom b) : Dom (a * b) := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_le_mul' (ha i j hij) (hb i j hij)

private theorem dom_of_val {n : ℕ} {a : Fin n → kˣ} (h : ∀ i, valuation k (a i : k) = 1) : Dom a := by
  intro i j _
  rw [h i, h j]

end Dominance

private theorem dom_cone {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {t y : kˣ} (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2)
    (h1 : valuation k (unif k : k) ≤ valuation k (y : k)) (h2 : valuation k (y : k) ≤ 1) :
    Dom ![t * (unif k)⁻¹, y, (unif k)⁻¹] := by
  have hp : 0 < valuation k (unif k : k) := (Valuation.pos_iff _).2 (unif k).ne_zero
  apply dom_three
  · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_le_iff₀ hp]
    calc valuation k (t : k) ≤ valuation k (unif k : k) ^ 2 := ht.le
      _ = valuation k (unif k : k) * valuation k (unif k : k) := sq _
      _ ≤ valuation k (y : k) * valuation k (unif k : k) := by gcongr
  · rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact h2.trans ((one_le_inv₀ hp).2 (h1.trans h2))

theorem UpperTheory.V.Z.Sym.So.gSpec :
    UpperTheory.V.Z.Sym.So.GSpec := by
  intro F _ _ Δ A hA V _ _ B s _ u Θ hO
  classical
  have hdom_sg : ∀ d : ParN F 3, A.DomS d → A.DomS (SD.sg d) := fun d hd v hv => dom_rev (hd v hv)
  have hsgsg : ∀ d : ParN F 3, SD.sg (SD.sg d) = d := by
    intro d
    funext v i
    fin_cases i <;> simp [SD.sg]
  let σ : {d : ParN F 3 // A.DomS d} ≃ {d : ParN F 3 // A.DomS d} :=
    { toFun := fun a => ⟨SD.sg a.1, hdom_sg a.1 a.2⟩
      invFun := fun a => ⟨SD.sg a.1, hdom_sg a.1 a.2⟩
      left_inv := fun a => Subtype.ext (hsgsg a.1)
      right_inv := fun a => Subtype.ext (hsgsg a.1) }
  let uΛ : {d : ParN F 3 // A.DomS d} → Module.End ℂ ↥B.Forms := fun a => u a.1
  have hcomm : ∀ a b : {d : ParN F 3 // A.DomS d}, Commute (uΛ a) (uΛ b) := by
    intro a b
    show u a.1 * u b.1 = u b.1 * u a.1
    rw [← hO.mul _ _ a.2 b.2, ← hO.mul _ _ b.2 a.2, mul_comm]
  have hth : ∀ a, Θ * uΛ a = uΛ (σ a) * Θ := fun a => hO.th a.1 a.2
  obtain ⟨X, c, hX, htr⟩ := Tf.trTheta _ ↥B.Forms uΛ Θ σ hcomm hth
  have hev : ∀ χ ∈ X, ∃ w : ↥B.Forms, w ≠ 0 ∧ ∀ a, uΛ a w = χ a • w :=
    fun χ hχ => (Tf.eigVec _ ↥B.Forms uΛ hcomm χ).1 (hX χ hχ).1
  let ext : ({d : ParN F 3 // A.DomS d} → ℂ) → ParN F 3 → ℂ :=
    fun χ d => if h : A.DomS d then χ ⟨d, h⟩ else 0
  have hext : ∀ χ (d : ParN F 3) (h : A.DomS d), ext χ d = χ ⟨d, h⟩ := fun χ d h => dif_pos h
  have hlevdom : ∀ d : ParN F 3, (∀ v ∈ A.Sg, ∀ i, d v i ∈ (A.V v).H) → A.DomS d := by
    intro d hd v hv
    exact dom_of_val (fun i => (A.V v).H_le (hd v hv i))
  have hcancel : ∀ (w : ↥B.Forms), w ≠ 0 → ∀ (x y : ℂ), x • w = y • w → x = y := by
    intro w hw x y h
    by_contra hxy
    apply hw
    have h0 : (x - y) • w = 0 := by rw [sub_smul, h, sub_self]
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hxy)
  have key : ∀ i : {χ // χ ∈ X}, ∃ (bχ : ℂ) (βχ : Dat.Par F → ℂ),
      (∀ (t t' : Dat.Par F), A.Cone t → A.Cone t' → βχ (t * t') = βχ t * βχ t') ∧
      (∀ (t : Dat.Par F), A.Cone t → ∑ y ∈ A.Ys, ext i.1 (A.dG t y) = bχ * βχ t) ∧
      (bχ ≠ 0 → ∀ (a : Chs F), (∀ (t : Dat.Par F), A.Cone t → βχ t = A.exS a t) →
        ∀ (d : ParN F 3), A.DomS d → ext i.1 d = A.exG a d) := by
    rintro ⟨χ, hχ⟩
    obtain ⟨w, hw, hwe⟩ := hev χ hχ
    apply charShape F Δ A hA (ext χ)
    · intro d d' hd hd'
      have hdd : A.DomS (d * d') := fun v hv => dom_mul (hd v hv) (hd' v hv)
      rw [hext χ _ hdd, hext χ _ hd, hext χ _ hd']
      apply hcancel w hw
      rw [← hwe ⟨d * d', hdd⟩]
      show u (d * d') w = _
      rw [hO.mul d d' hd hd', Module.End.mul_apply]
      rw [show u d' w = χ ⟨d', hd'⟩ • w from hwe ⟨d', hd'⟩, map_smul,
        show u d w = χ ⟨d, hd⟩ • w from hwe ⟨d, hd⟩, smul_smul, mul_comm]
    · intro d hd
      have hD := hlevdom d hd
      rw [hext χ d hD]
      apply hcancel w hw
      rw [← hwe ⟨d, hD⟩, one_smul]
      show u d w = w
      rw [hO.lev d hd]
      rfl
    · intro d hd
      rw [hext χ _ (hdom_sg d hd), hext χ d hd]
      exact (hX χ hχ).2 ⟨d, hd⟩
  choose b β hβm hβs hβe using key
  refine ⟨{χ // χ ∈ X}, Finset.univ, fun i => c i.1 * b i, β, ?_, ?_, ?_⟩
  · intro i _ t t' ht ht'
    exact hβm i t t' ht ht'
  · intro t ht
    have hdG : ∀ y ∈ A.Ys, A.DomS (A.dG t y) := by
      intro y hy v hv
      have hyv : y ⟨v, hv⟩ ∈ A.Ry v := Fintype.mem_piFinset.1 hy ⟨v, hv⟩
      have hr := (hA.ry v hv).1 _ hyv
      show Dom ![t v * (unif (Kv v))⁻¹, if h : v ∈ A.Sg then y ⟨v, h⟩ else 1, (unif (Kv v))⁻¹]
      rw [dif_pos hv]
      exact dom_cone (ht v hv) hr.1 hr.2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hO.tr t ht, map_sum]
    have h1 : ∀ y ∈ A.Ys, LinearMap.trace ℂ ↥B.Forms (u (A.dG t y) * Θ) =
        ∑ χ ∈ X, c χ * ext χ (A.dG t y) := by
      intro y hy
      rw [show u (A.dG t y) = uΛ ⟨_, hdG y hy⟩ from rfl, htr]
      exact Finset.sum_congr rfl fun χ _ => by rw [hext χ _ (hdG y hy)]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, ← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hβs i t ht, mul_assoc]
  · rintro ⟨χ, hχ⟩ _ hb a ha
    have hb' : b ⟨χ, hχ⟩ ≠ 0 := right_ne_zero_of_mul hb
    obtain ⟨w, hw, hwe⟩ := hev χ hχ
    refine ⟨(w : GA Δ → V), w.2, fun h => hw (Subtype.ext h), ?_⟩
    intro d g hd hg
    rw [← hO.eq d g hd hg w, ← hβe ⟨χ, hχ⟩ hb' a ha d hd, hext χ d hd]
    rw [show u d w = χ ⟨d, hd⟩ • w from hwe ⟨d, hd⟩]
    rfl

end
end

