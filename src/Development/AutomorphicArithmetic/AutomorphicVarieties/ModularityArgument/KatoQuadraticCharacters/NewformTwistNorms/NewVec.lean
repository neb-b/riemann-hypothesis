module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0011

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace UpperTheory.V.Z.Kato.NewVec

open UpperTheory.V.Sd

private theorem comp_zero {V : Type} [AddCommGroup V] [Module ℂ V] {U W : Submodule ℂ V} (hd : Disjoint U W) (T : Module.End ℂ V)
    (hU : ∀ x ∈ U, T x ∈ U) (hW : ∀ x ∈ W, T x ∈ W) {φ ψ : V} (hψ : ψ ∈ U) (hm : φ - ψ ∈ W) (h0 : T φ = 0) : T ψ = 0 := by
  refine Submodule.disjoint_def.1 hd _ (hU _ hψ) ?_
  have := W.neg_mem (hW _ hm)
  rwa [map_sub, h0, zero_sub, neg_neg] at this

private noncomputable abbrev Eo (v : InfinitePlace ℚ) (i j : Fin 2) : Module.End ℂ (TR.Sm ℚ 2) := TR.Eop v i j

private theorem eop_mem {U : Submodule ℂ (TR.Sm ℚ 2)} (hU : TR.IsStable U) (v : InfinitePlace ℚ) (i j : Fin 2) :
    ∀ x ∈ U, TR.Eop v i j x ∈ U := fun x hx => hU (.lie _) x hx

private theorem eop_one (v : InfinitePlace ℚ) (φ : TR.Sm ℚ 2) :
    TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = TR.lie ℚ 2 (TR.oneL ℚ 2) φ := by
  classical
  rw [TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
  congr 2
  ext i j w
  obtain rfl : w = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp

theorem newVec : Published.CuspSemisimpleReal → Published.AdmissibleReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k), ∃ (π₀ : TR.CuspSub ℚ 2) (ψ : TR.Sm ℚ 2), ψ ∈ π₀.V ∧ ψ ≠ 0 ∧ (∀ q : HeightOneSpectrum (𝓞 ℚ), ψ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev g.M q))) ∧ ((∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = (Complex.I * (k : ℂ)) • ψ) ∧ (∀ v, TR.Eop v 0 0 ψ - TR.Eop v 1 1 ψ = Complex.I • (TR.Eop v 0 1 ψ + TR.Eop v 1 0 ψ)) ∧ (∀ v, TR.Eop v 0 0 ψ + TR.Eop v 1 1 ψ = 0)) ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M) := by
  intro hS hA k hk2 f
  have hM : 1 ≤ f.M := f.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar f.M hM f.χ
  obtain ⟨hfin, hval⟩ := charVal f.M hM f.χ ω hω
  have hLift : LiftHol := by
    intro k M hM χ ω hω f hf
    obtain ⟨φ₀, hφ⟩ := liftEx k M hM f fun δ hδ =>
      SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩
    obtain ⟨hl, hr, hs⟩ := liftSm k M hM f φ₀ hφ
    let φ : TR.Sm ℚ 2 := ⟨φ₀, hs f.holo'⟩
    have hfix : ∀ u ∈ K1G M, TR.finRep ℚ 2 u φ = φ :=
      fun u hu => Subtype.ext (funext (hr u hu))
    have hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ} :=
      isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen M hM).1.mem_nhds (one_mem _)) hfix)
    have hc := liftCent k M hM χ ω hω f hf φ₀ hφ
    have hlie := liftLie k M hM f f.holo' φ hφ
    obtain ⟨C, hC⟩ := archBd k M hM f
    have haut : TR.IsAutForm φ := ⟨hl, hlev, liftK k M hM f φ hφ,
      zFin ℚ k ω (charVal M hM χ ω hω).1 φ hc (fun v => (hlie v).1) (fun v => (hlie v).2),
      fun g => ⟨C, 0, fun y => by
        obtain ⟨γ, h, u, hu, e⟩ := decomp M hM (g * TR.infGL ℚ 2 y)
        rw [pow_zero, mul_one, e]
        change ‖φ₀ _‖ ≤ C
        rw [hφ γ h u hu]
        exact hC _ h.det_ne_zero⟩⟩
    exact ⟨φ, hφ, ⟨haut, fun w u hu => hfix _ (kLocal M hM w u hu), hc,
      fun v => (hlie v).1, fun v => (hlie v).2⟩, haut, cuspCrit φ hl hlev (liftCT k M hM f φ₀ hφ)⟩
  obtain ⟨φ, hL, hH, hC⟩ := hLift k f.M hM f.χ ω hω f.f f.char
  have hE := liftExp k f.M hM f.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev f.M) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, f.one] at this
    exact one_ne_zero this
  obtain ⟨h1, -⟩ := holCap ℚ k _ ω hfin φ hH
  obtain ⟨π, ψ, W, hψ, hW, hd, hm⟩ := split ℚ 2 φ h0 (hS ℚ 2 φ hC ⟨0, by rw [h1, zero_smul]⟩)
  have hπ : TR.IsStable π.V := π.stable
  refine ⟨π, ψ.1, ψ.2, fun e => hψ (Subtype.ext e), fun q u hu => ?_, ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩, fun w hw => ?_⟩
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U, (locSm ℚ q u - 1 : Module.End ℂ _) x ∈ U :=
      fun U hU x hx => U.sub_mem (hU (.fin (locGL ℚ 2 q u)) x hx) hx
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.level q u hu)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 1 - Eo v 1 0 - (Complex.I * (k : ℂ)) • (1 : Module.End ℂ (TR.Sm ℚ 2))) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)) (U.smul_mem _ hx)
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.wt v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 - Eo v 1 1 - Complex.I • (Eo v 0 1 + Eo v 1 0)) x ∈ U :=
      fun U hU x hx => U.sub_mem (U.sub_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx))
        (U.smul_mem _ (U.add_mem (eop_mem hU v 0 1 x hx) (eop_mem hU v 1 0 x hx)))
    exact sub_eq_zero.1 (comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm (sub_eq_zero.2 (hH.low v)))
  · have key : ∀ U : Submodule ℂ (TR.Sm ℚ 2), TR.IsStable U → ∀ x ∈ U,
        (Eo v 0 0 + Eo v 1 1) x ∈ U :=
      fun U hU x hx => U.add_mem (eop_mem hU v 0 0 x hx) (eop_mem hU v 1 1 x hx)
    exact comp_zero hd _ (key _ hπ) (key _ hW) ψ.2 hm ((eop_one v φ).trans h1)
  · have hc := (places w).2.2.2 f.M hM hw
    obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
    obtain ⟨c₀, h3⟩ := h2 _ _ hE
    have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE)
      fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]
    rw [hc, neg_smul, add_neg_eq_zero] at h4
    obtain ⟨α, β, hv, hsum, hprod⟩ := satHol ℚ k _ ω φ hH h0 w _ hc h4
    exact ⟨α, β, satOfVec hA ℚ 2 π w ψ _ (satComp ℚ φ π ψ W hψ hW hd hm w _ hv), hsum, by rw [hprod, hval w hw]⟩

end UpperTheory.V.Z.Kato.NewVec
