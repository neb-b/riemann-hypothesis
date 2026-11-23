module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSeenTr
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep

private theorem hint_fst {G P : Type} [Group G] [Group P] [Subsingleton P] (K N : Subgroup G) (K' : Subgroup P)
    (u : G × P → ℂ) (hNK : N ≤ K) (hu : ∀ k ∈ N, ∀ x, u (x * k, 1) = u (x, 1)) (hi : N.relIndex K ≠ 0) :
    hint (K.prod K') u = ((N.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ N, u (q.out, 1) := by
  have hp : ∀ z : G × P, z = (z.1, 1) := fun z => Prod.ext rfl (Subsingleton.elim _ _)
  set L : Subgroup (G × P) := N.comap (MonoidHom.fst G P) with hL
  have hmap : (K.prod K').map (MonoidHom.fst G P) = K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      exact ⟨(x, 1), ⟨hx, K'.one_mem⟩, rfl⟩
  have hrel : L.relIndex (K.prod K') = N.relIndex K := by
    rw [hL, Subgroup.relIndex_comap, hmap]
  have hLK : L ≤ K.prod K' := fun z hz => by
    rw [hp z]
    exact ⟨hNK hz, K'.one_mem⟩
  have hLu : L ≤ rStab u := fun k hk x => by
    have h1 : x * k = (x.1 * k.1, 1) := Prod.ext rfl (Subsingleton.elim _ _)
    rw [h1, hu k.1 hk x.1, ← hp x]
  rw [_root_.GlobalTheory.BCT.HintLevel.hint_level _ _ L u hLK hLu (by rwa [hrel]), hrel]
  congr 1
  have hval : ∀ q : G ⧸ N, u (Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) = u (q.out, 1) := by
    intro q
    have hm : ((q.out, (1 : P)))⁻¹ * Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) ∈ L :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    obtain ⟨k, hk⟩ : ∃ k : G × P, k ∈ L ∧ Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) = (q.out, 1) * k :=
      ⟨_, hm, (mul_inv_cancel_left _ _).symm⟩
    rw [hk.2]
    exact hLu hk.1 _
  have hbij : Function.Bijective (fun q : G ⧸ N => (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) := by
    constructor
    · intro a b hab
      have h := QuotientGroup.eq.mp hab
      have h2 : (a.out)⁻¹ * b.out ∈ N := by simpa [hL] using h
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      exact QuotientGroup.eq.mpr h2
    · intro c
      induction c using QuotientGroup.induction_on with
      | H z =>
        refine ⟨QuotientGroup.mk z.1, QuotientGroup.eq.mpr ?_⟩
        have h3 : ((QuotientGroup.mk z.1 : G ⧸ N).out)⁻¹ * z.1 ∈ N :=
          QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
        simpa [hL] using h3
  rw [← finsum_comp _ hbij]
  exact finsum_congr hval

private theorem tr_core (hTr : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel) (hCv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp)
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K N : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hNo : IsOpen (N : Set G)) (hNc : IsCompact (N : Set G)) (hNK : N ≤ K)
    (hi : ((N.relIndex K : ℕ) : ℂ) ≠ 0) (hfd : FiniteDimensional ℂ (fixed ρ N))
    (f₁ f₂ F : G → ℂ) (h₁ : IsHecke N f₁) (h₂ : IsHecke N f₂)
    (hFeq : F = fun g => ((N.relIndex K : ℕ) : ℂ)⁻¹ * UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂ g) :
    trOn (fixed ρ N) (Lv ρ N f₁ * Lv ρ N f₂) = ((N.relIndex K : ℕ) : ℂ) ^ 2 * trc ρ K F := by
  set i : ℂ := ((N.relIndex K : ℕ) : ℂ) with hidef
  have hcvH : IsHecke N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) :=
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cvHecke _ N hNo hNc f₁ f₂ h₁ h₂
  have hFH : IsHecke N F := by
    refine ⟨?_, ?_⟩
    · rw [hFeq]
      exact hcvH.1.mul_left (f := fun _ => i⁻¹)
    · intro k hk x
      rw [hFeq]
      simp only
      rw [(hcvH.2 k hk x).1, (hcvH.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  have hNK₁ : N ≤ K ⊓ rStab F ⊓ rStab fun y => F y⁻¹ := by
    refine le_inf (le_inf hNK ?_) ?_
    · exact fun k hk x => (hFH.2 k hk x).2
    · intro k hk x
      have e : (x * k)⁻¹ = k⁻¹ * x⁻¹ := by group
      show F (x * k)⁻¹ = F x⁻¹
      rw [e]
      exact (hFH.2 k⁻¹ (N.inv_mem hk) _).1
  have hK₁H : IsHecke (K ⊓ rStab F ⊓ rStab fun y => F y⁻¹) F := by
    refine ⟨hFH.1, fun k hk x => ⟨?_, hk.1.2 x⟩⟩
    have hk' : k⁻¹ ∈ rStab fun y => F y⁻¹ := (rStab _).inv_mem hk.2
    have := hk' x⁻¹
    simpa using this
  have hlev := hTr G K hKo hKc V ρ F _ N hNo hNK₁ (inf_le_left.trans inf_le_left) hK₁H hfd
  have hop : levOp ρ K N F LinearMap.id = i⁻¹ • i⁻¹ • levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id := by
    rw [hFeq]
    unfold levOp
    rw [Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    congr 1
    rw [smul_finsum]
    exact finsum_congr fun q => by rw [mul_smul]
  have hmul : ∀ v ∈ fixed ρ N, levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id v = (Lv ρ N f₁ * Lv ρ N f₂) v :=
    fun v hv => (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).1
  have hpres : ∀ v ∈ fixed ρ N, (Lv ρ N f₁ * Lv ρ N f₂) v ∈ fixed ρ N := fun v hv =>
    (hCv G N hNo hNc V ρ f₂ f₁ h₂ h₁ _ (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).2.1).2.1
  have hstab : ∀ v ∈ fixed ρ N, levOp ρ K N F LinearMap.id v ∈ fixed ρ N := fun v hv => by
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v hv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hpres v hv))
  have hres : (levOp ρ K N F LinearMap.id).restrict hstab = (i⁻¹ * i⁻¹) • (Lv ρ N f₁ * Lv ρ N f₂).restrict hpres := by
    ext v
    simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v v.2, mul_smul]
  unfold trc
  rw [← hlev]
  unfold twTr trOn
  rw [dite_eq_left hstab, dite_eq_left hpres, hres, map_smul, smul_eq_mul]
  field_simp

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.seenTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SeenTr := by
  intro hTr hAdm hCv E _ _ _ n w hw τ N hNo hNK
  obtain ⟨-, -, hKo, hKc, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w
  have hNc : IsCompact (N : Set (GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  haveI : Finite ((KGL w (n := n) : Subgroup (GLw n w)) ⧸ N.subgroupOf (KGL w (n := n))) :=
    GlobalTheory.TwTrLevel.finite_quot (KGL w (n := n)) (KGL w (n := n)) N hKc hKo hNo le_rfl
  have hi : N.relIndex (KGL w (n := n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiC : ((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  refine ⟨((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ^ 2, pow_ne_zero _ hiC, ?_⟩
  intro φ₁ φ₂ hb
  refine tr_core hTr hCv τ.ρ (KGL w (n := n)) N hKo hKc hNo hNc hNK hiC (hAdm E n w τ N hNo) _ _ _ (hb false) (hb true) ?_
  funext g
  have h₁ := hb false
  have h₂ := hb true
  have hr : ∀ k ∈ N, ∀ x : GLw n w, two φ₁ φ₂ w false (x * k) * two φ₁ φ₂ w true ((x * k)⁻¹ * g) =
      two φ₁ φ₂ w false x * two φ₁ φ₂ w true (x⁻¹ * g) := by
    intro k hk x
    have e : (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) := by group
    rw [e, (h₁.2 k hk x).2, (h₂.2 k⁻¹ (N.inv_mem hk) _).1]
  have hcv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N (two φ₁ φ₂ w false) (two φ₁ φ₂ w true) g =
      ∑ᶠ q : GLw n w ⧸ N, two φ₁ φ₂ w false q.out * two φ₁ φ₂ w true (q.out⁻¹ * g) := by
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
    rw [_root_.GlobalTheory.BCT.HintLevel.hint_level _ N N _ le_rfl (fun k hk x => hr k hk x) (by simp)]
    simp
  have hpr : ∀ x : GLw n w, ((x, 1) : GLw n w × GLw 0 w)⁻¹ * (g, 1) = (x⁻¹ * g, 1) := fun x =>
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [hcv]
  unfold PositivityTheory.Rg.BcB.G8.seen
  rw [if_pos hw]
  rw [hint_fst (KGL w (n := n)) N (KGL w (n := 0)) _ hNK ?_ hi]
  · congr 1
    refine finsum_congr fun q => ?_
    rw [hpr]
    rfl
  · intro k hk x
    rw [hpr, hpr]
    exact hr k hk x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSimpleFix
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors

open GlobalTheory.PRep GlobalTheory.BCT GlobalTheory.TwTrLevel

section

variable {G : Type} [Group G]

private def Mg (N : Subgroup G) (g : G) : Subgroup G := N ⊓ N.comap (MulAut.conj g⁻¹).toMonoidHom

private theorem mem_Mg (N : Subgroup G) (g m : G) : m ∈ Mg N g ↔ m ∈ N ∧ g⁻¹ * m * g ∈ N := by
  simp [Mg, Subgroup.mem_comap, MulAut.conj_apply]

private def dc (N : Subgroup G) (g : G) : Set G := {y | ∃ a ∈ N, ∃ b ∈ N, y = a * g * b}

private theorem dc_left (N : Subgroup G) (g : G) {k : G} (hk : k ∈ N) (x : G) : k * x ∈ dc N g ↔ x ∈ dc N g := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨k⁻¹ * a, N.mul_mem (N.inv_mem hk) ha, b, hb, ?_⟩
    simp only [mul_assoc] at e ⊢
    rw [eq_inv_mul_iff_mul_eq]
    exact e
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨k * a, N.mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩

private theorem dc_right (N : Subgroup G) (g : G) {k : G} (hk : k ∈ N) (x : G) : x * k ∈ dc N g ↔ x ∈ dc N g := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b * k⁻¹, N.mul_mem hb (N.inv_mem hk), ?_⟩
    rw [← mul_assoc, ← e]
    simp
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * k, N.mul_mem hb hk, by simp only [mul_assoc]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isOpen_Mg (N : Subgroup G) (hNo : IsOpen (N : Set G)) (g : G) : IsOpen (Mg N g : Set G) := by
  have e : (Mg N g : Set G) = (N : Set G) ∩ (fun m => g⁻¹ * m * g) ⁻¹' (N : Set G) := by
    ext m
    simp [mem_Mg]
  rw [e]
  exact hNo.inter (hNo.preimage (by fun_prop))

private theorem hecke_dc (N : Subgroup G) (hNc : IsCompact (N : Set G)) (g : G) :
    IsHecke N ((dc N g).indicator 1) := by
  refine ⟨?_, ?_⟩
  · have hc : IsCompact (dc N g) := by
      have e : dc N g = (fun p : G × G => p.1 * g * p.2) '' ((N : Set G) ×ˢ (N : Set G)) := by
        ext y
        constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
          exact ⟨a, ha, b, hb, rfl⟩
      rw [e]
      exact (hNc.prod hNc).image (by fun_prop)
    exact hc.closure_of_subset Set.support_indicator_subset
  · intro k hk x
    constructor
    · by_cases h : x ∈ dc N g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_left N g hk x).2 h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((dc_left N g hk x).1 h')]
    · by_cases h : x ∈ dc N g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_right N g hk x).2 h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((dc_right N g hk x).1 h')]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem fixed_Mg (ρ : Representation ℂ G V) (N : Subgroup G) (g : G) (x : V) (hx : x ∈ fixed ρ N) :
    ρ g x ∈ fixed ρ (Mg N g) := by
  rw [mem_fixed_iff] at hx ⊢
  intro m hm
  have h := hx _ ((mem_Mg N g m).1 hm).2
  have e : m * g = g * (g⁻¹ * m * g) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h]

private theorem lv_dc (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (g : G) (x : V) (hx : x ∈ fixed ρ N) :
    levOp ρ N N ((dc N g).indicator 1) LinearMap.id x =
      ∑ᶠ j : N ⧸ (Mg N g).subgroupOf N, ρ (j.out : G) (ρ g x) := by
  have hH := hecke_dc N hNc g
  have hs := finite_supp N hNo _ hH.1
  have hx' := (mem_fixed_iff ρ N x).1 hx
  rw [levOp_apply ρ N N _ _ x hs, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_smul, LinearMap.id_apply]
  set f : G → ℂ := (dc N g).indicator 1 with hf
  set F : G → V := fun y => f y • ρ y x with hF
  have hFr : ∀ y, ∀ h ∈ N, F (y * h) = F y := by
    intro y h hh
    simp only [hF, (hH.2 h hh y).2, map_mul, Module.End.mul_apply, hx' h hh]
  let Φ : N ⧸ (Mg N g).subgroupOf N → G ⧸ N := fun j => QuotientGroup.mk ((j.out : G) * g)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h1 : ((a.out : G) * g)⁻¹ * ((b.out : G) * g) ∈ N := QuotientGroup.eq.1 hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ((mem_Mg N g _).2 ⟨?_, ?_⟩))
    · exact N.mul_mem (N.inv_mem (a.out).2) (b.out).2
    · have e : g⁻¹ * (((a.out⁻¹ * b.out : N)) : G) * g = ((a.out : G) * g)⁻¹ * ((b.out : G) * g) := by
        simp [mul_assoc]
      rw [e]
      exact h1
  have hsup : Function.support (fun q : G ⧸ N => F q.out) ⊆ Set.range Φ := by
    intro q hq
    have hne : f q.out ≠ 0 := by
      intro h0
      exact hq (by simp [hF, h0])
    have hmem : q.out ∈ dc N g := by
      by_contra hn
      exact hne (Set.indicator_of_notMem hn _)
    obtain ⟨a, ha, b, hb, e⟩ := hmem
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((Mg N g).subgroupOf N) (⟨a, ha⟩ : N)
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    have hm' := (mem_Mg N g _).1 (Subgroup.mem_subgroupOf.1 m.2)
    show QuotientGroup.mk (((QuotientGroup.mk (⟨a, ha⟩ : N) : N ⧸ (Mg N g).subgroupOf N).out : G) * g) = q
    rw [hm, ← QuotientGroup.out_eq' q, e]
    refine QuotientGroup.eq.2 ?_
    have e2 : ((((⟨a, ha⟩ : N) * (m : N) : N) : G) * g)⁻¹ * (a * g * b) =
        (g⁻¹ * ((m : N) : G) * g)⁻¹ * b := by
      simp [mul_assoc]
    rw [e2]
    exact N.mul_mem (N.inv_mem hm'.2) hb
  change ∑ᶠ q : G ⧸ N, F q.out = _
  have hR : ∑ᶠ q ∈ Set.range Φ, F (Quotient.out q) = ∑ᶠ q : G ⧸ N, F (Quotient.out q) := by
    rw [← finsum_mem_inter_support (fun q : G ⧸ N => F (Quotient.out q)) (Set.range Φ), Set.inter_eq_right.2 hsup,
      finsum_mem_support]
  rw [← hR, finsum_mem_range hinj]
  refine finsum_congr fun j => ?_
  have h1 : F (Φ j).out = F ((j.out : G) * g) := out_eq_of_inv N F (fun y h hh => hFr y h hh) _
  rw [h1]
  have hmem : (j.out : G) * g ∈ dc N g := ⟨j.out, (j.out).2, 1, N.one_mem, by simp⟩
  simp [hF, hf, Set.indicator_of_mem hmem, map_mul, Module.End.mul_apply]

private theorem avg_dc (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (g : G) (x : V) (hx : x ∈ fixed ρ N) [Finite (N ⧸ (Mg N g).subgroupOf N)] :
    avgOp ρ N (Mg N g) (ρ g x) =
      (((Mg N g).relIndex N : ℕ) : ℂ)⁻¹ • levOp ρ N N ((dc N g).indicator 1) LinearMap.id x := by
  rw [avgOp_apply, lv_dc ρ N hNo hNc g x hx]

private theorem avg_level (ρ : Representation ℂ G V) (N M M' : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (hMo : IsOpen (M : Set G)) (hM'o : IsOpen (M' : Set G)) (hMN : M ≤ N)
    (hle : M' ≤ M) (v : V) (hv : v ∈ fixed ρ M) : avgOp ρ N M' v = avgOp ρ N M v := by
  haveI h1 := finite_quot N N M' hNc hNo hM'o le_rfl
  haveI h2 := finite_quot N N M hNc hNo hMo le_rfl
  haveI h3 := finite_quot N M M' hNc hMo hM'o hMN
  haveI h4 := finite_quot N N (Mg N 1) hNc hNo (isOpen_Mg N hNo 1) le_rfl
  have hH := hecke_dc N hNc 1
  have hHM : IsHecke M ((dc N 1).indicator 1) := ⟨hH.1, fun k hk y => hH.2 k (hMN hk) y⟩
  have hvM' : v ∈ fixed ρ M' := by
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  have e1 := levOp_le ρ N N M' (hle.trans hMN) le_rfl hNo hM'o _ hH v hvM'
  have e2 := levOp_le ρ N M M' hle hMN hMo hM'o _ hHM v hvM'
  rw [avgOp_fix ρ M M' v hv] at e2
  have e3 := levOp_le ρ N N M hMN le_rfl hNo hMo _ hH v hv
  have back : ∀ y ∈ fixed ρ N, y = (((Mg N 1).relIndex N : ℕ) : ℂ)⁻¹ •
      levOp ρ N N ((dc N 1).indicator 1) LinearMap.id y := by
    intro y hy
    rw [← avg_dc ρ N hNo hNc 1 y hy, map_one, Module.End.one_apply, avgOp_fix ρ N _ y hy]
  rw [back _ (avgOp_mem ρ N M' v hvM'), back _ (avgOp_mem ρ N M v hv), ← e1, e2, e3]

private theorem core (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G))
    (hirr : ∀ W : Submodule ℂ V, (∀ g x, x ∈ W → ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule ℂ V) (hW : W ≤ fixed ρ N)
    (hst : ∀ f, IsHecke N f → ∀ x ∈ W, levOp ρ N N f LinearMap.id x ∈ W) : W = ⊥ ∨ W = fixed ρ N := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  refine Or.inr (le_antisymm hW ?_)
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hb
  have hxN := hW hxW
  let O : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hxO : x ∈ O := Submodule.subset_span ⟨1, by simp⟩
  have hO : O = ⊤ := by
    have hinv : ∀ g y, y ∈ O → ρ g y ∈ O := by
      intro g y hy
      refine Submodule.span_induction (p := fun y _ => ρ g y ∈ O) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, rfl⟩
        refine Submodule.subset_span ⟨g * a, ?_⟩
        simp [map_mul, Module.End.mul_apply]
      · simp
      · intro a b _ _ ha hb
        rw [map_add (f := _)]
        exact O.add_mem ha hb
      · intro c a _ ha
        rw [map_smul]
        exact O.smul_mem c ha
    rcases hirr O hinv with h | h
    · exact absurd (by simpa [h] using hxO) hx0
    · exact h
  have hp : ∀ v ∈ O, ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ N ∧ v ∈ fixed ρ M ∧ avgOp ρ N M v ∈ W := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ N ∧
      v ∈ fixed ρ M ∧ avgOp ρ N M v ∈ W) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g, rfl⟩
      haveI := finite_quot N N (Mg N g) hNc hNo (isOpen_Mg N hNo g) le_rfl
      refine ⟨Mg N g, isOpen_Mg N hNo g, inf_le_left, fixed_Mg ρ N g x hxN, ?_⟩
      show avgOp ρ N (Mg N g) (ρ g x) ∈ W
      rw [avg_dc ρ N hNo hNc g x hxN]
      exact W.smul_mem _ (hst _ (hecke_dc N hNc g) x hxW)
    · exact ⟨N, hNo, le_rfl, (fixed ρ N).zero_mem, by simp⟩
    · rintro a b _ _ ⟨M₁, ho₁, hl₁, hf₁, hw₁⟩ ⟨M₂, ho₂, hl₂, hf₂, hw₂⟩
      have ho : IsOpen ((M₁ ⊓ M₂ : Subgroup G) : Set G) := ho₁.inter ho₂
      have hm : ∀ (M : Subgroup G) (y : V), M₁ ⊓ M₂ ≤ M → y ∈ fixed ρ M → y ∈ fixed ρ (M₁ ⊓ M₂) := by
        intro M y hle hy
        rw [mem_fixed_iff] at hy ⊢
        exact fun h hh => hy h (hle hh)
      refine ⟨M₁ ⊓ M₂, ho, inf_le_left.trans hl₁,
        (fixed ρ _).add_mem (hm _ _ inf_le_left hf₁) (hm _ _ inf_le_right hf₂), ?_⟩
      rw [map_add (f := _), avg_level ρ N M₁ _ hNo hNc ho₁ ho hl₁ inf_le_left a hf₁,
        avg_level ρ N M₂ _ hNo hNc ho₂ ho hl₂ inf_le_right b hf₂]
      exact W.add_mem hw₁ hw₂
    · rintro c a _ ⟨M, ho, hl, hf, hw⟩
      refine ⟨M, ho, hl, (fixed ρ M).smul_mem c hf, ?_⟩
      rw [map_smul]
      exact W.smul_mem c hw
  intro z hz
  obtain ⟨M, ho, hl, -, hw⟩ := hp z (hO ▸ Submodule.mem_top)
  haveI := finite_quot N N M hNc hNo ho le_rfl
  rwa [avgOp_fix ρ N M z hz] at hw

end

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.simpleFix_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SimpleFix := by
  intro _ E _ _ _ n w τ N hNo hNle
  have hKc := (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w).2.2.2.1
  have hNc : IsCompact (N : Set (GlobalTheory.BCT.GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNle
  obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ.ρ).1 τ.irred
  refine ⟨fun f hf x hx => GlobalTheory.TraceLevel.levOp_mem_fixed τ.ρ N N N f hf hNo le_rfl x hx, ?_⟩
  exact fun W hW hst => UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors.core τ.ρ N hNo hNc hirr W hW hst
end

