module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.HeckeComp
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F
open PositivityTheory.RgTw (Mat G)

private theorem hecke_comp {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {φ : G → G} (hc : Continuous φ)
    (hi : ∀ g, φ (φ g) = g) (hm : ∀ a b, φ (a * b) = φ a * φ b) (hK : ∀ k ∈ K, φ k ∈ K) {h : G → ℂ}
    (hh : IsHecke K h) : IsHecke K (fun g => h (φ g)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · let e : G ≃ₜ G :=
      { toFun := φ, invFun := φ, left_inv := hi, right_inv := hi,
        continuous_toFun := hc, continuous_invFun := hc }
    exact hh.1.comp_homeomorph e
  · simp only [hm]
    exact hh.2 _ (hK k hk) _

private theorem core {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (hS : LvShift) (ρ : Representation ℂ G V) (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (u : G) (hu : ∀ x, x ∈ K ↔ u * x * u⁻¹ ∈ K) (θ : G → G)
    (hθc : Continuous θ) (hθi : ∀ g, θ (θ g) = g) (hθm : ∀ a b, θ (a * b) = θ a * θ b) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hθu : θ u = u⁻¹) (Y : Submodule ℂ V) (hY : Y ≤ fixed ρ K) (r : (G → ℂ) → Module.End ℂ Y)
    (hact : ∀ h, IsHecke K h → ∀ y : Y, (r h y : V) = Lv ρ K h y)
    (A : Module.End ℂ Y) (hAA : A * A = 1)
    (hA : ∀ h, IsHecke K h → A * r h = r (fun g => h (θ g)) * A) :
    (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) = 1 ∧
    (∀ h, IsHecke K h → (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * r h =
      r (fun g => h (u * θ g * u⁻¹)) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A)) ∧
    ∀ h, IsHecke K h → IsHecke K (fun g => h (g * u⁻¹)) ∧
      r (fun g => h (g * u⁻¹)) = r h * r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) := by
  have h0 : IsHecke K (0 : G → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have Sh := hS G V ρ K ho hc
  have hI : IsHecke K ((K : Set G).indicator 1) := (Sh u hu 0 h0).2.2.1
  have hu' : ∀ x, x ∈ K ↔ u⁻¹ * x * u⁻¹⁻¹ ∈ K := fun x => by
    rw [hu (u⁻¹ * x * u⁻¹⁻¹)]
    simp [mul_assoc]

  have a1 : ∀ v : G, (∀ x, x ∈ K ↔ v * x * v⁻¹ ∈ K) → ∀ y : Y,
      (r (fun g => (K : Set G).indicator 1 (v⁻¹ * g)) y : V) = ρ v y := fun v hv y => by
    obtain ⟨-, hl, -, -⟩ := Sh v hv _ hI
    obtain ⟨-, -, e1, e2⟩ := (Sh v hv _ hI).2.2.2 y (hY y.2)
    rw [hact _ hl, e1, e2]
  set Ru := r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) with hRu
  set Ru' := r (fun g => (K : Set G).indicator 1 (u * g)) with hRu'
  have b1 : ∀ y : Y, (Ru y : V) = ρ u y := a1 u hu
  have b2 : ∀ y : Y, (Ru' y : V) = ρ u⁻¹ y := fun y => by
    have := a1 u⁻¹ hu' y
    simpa only [inv_inv] using this
  have hRR : Ru * Ru' = 1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show (Ru (Ru' y) : V) = y
    rw [b1, b2, ← Module.End.mul_apply, ← map_mul]
    simp
  have hAR : A * Ru = Ru' * A := by
    rw [hRu, hA _ (Sh u hu _ hI).2.1, hRu']
    congr 2
    funext g
    have e : u⁻¹ * θ g = θ (u * g) := by rw [hθm, hθu]
    have m : θ (u * g) ∈ K ↔ u * g ∈ K :=
      ⟨fun h => by simpa only [hθi] using hθK _ h, hθK _⟩
    rw [e]
    by_cases c : u * g ∈ K
    · rw [Set.indicator_of_mem (by exact_mod_cast m.2 c), Set.indicator_of_mem (by exact_mod_cast c)]
      rfl
    · rw [Set.indicator_of_notMem (by exact_mod_cast fun d => c (m.1 d)), Set.indicator_of_notMem (by exact_mod_cast c)]
  have hθu' : θ u⁻¹ = u := by rw [← hθu, hθi]
  refine ⟨?_, fun h hh => ?_, fun h hh => ?_⟩
  · calc (Ru * A) * (Ru * A) = Ru * (A * Ru) * A := by simp only [mul_assoc]
      _ = (Ru * Ru') * (A * A) := by rw [hAR]; simp only [mul_assoc]
      _ = 1 := by rw [hRR, hAA, one_mul]
  · have hf : IsHecke K (fun g => h (θ g)) := hecke_comp hθc hθi hθm hθK hh
    have hf' : IsHecke K (fun g => h (u * θ g * u⁻¹)) := by
      refine hecke_comp (φ := fun g => u * θ g * u⁻¹) (by fun_prop) (fun g => ?_) (fun a b => ?_) (fun k hk => ?_) hh
      · show u * θ (u * θ g * u⁻¹) * u⁻¹ = g
        rw [hθm, hθm, hθu, hθu', hθi]
        group
      · show u * θ (a * b) * u⁻¹ = u * θ a * u⁻¹ * (u * θ b * u⁻¹)
        rw [hθm]
        group
      · exact (hu _).1 (hθK k hk)
    have e : Ru * r (fun g => h (θ g)) = r (fun g => h (u * θ g * u⁻¹)) * Ru := by
      refine LinearMap.ext fun y => Subtype.ext ?_
      show (Ru (r (fun g => h (θ g)) y) : V) = (r (fun g => h (u * θ g * u⁻¹)) (Ru y) : V)
      obtain ⟨p1, p2, -⟩ := Sh u hu _ hf
      obtain ⟨q1, q2, -⟩ := Sh u hu _ hf'
      obtain ⟨-, -, e1, -⟩ := (Sh u hu _ hf).2.2.2 y (hY y.2)
      obtain ⟨-, e2, -, -⟩ := (Sh u hu _ hf').2.2.2 y (hY y.2)
      have ef : (fun g => h (θ (u⁻¹ * g))) = fun g => h (u * θ (g * u⁻¹) * u⁻¹) := by
        funext g
        rw [hθm, hθm, hθu']
        congr 1
        group
      rw [b1, hact _ hf, hact _ hf', b1, ← e1, ← e2, ef]
    calc (Ru * A) * r h = Ru * (A * r h) := by rw [mul_assoc]
      _ = (Ru * r (fun g => h (θ g))) * A := by rw [hA h hh, mul_assoc]
      _ = r (fun g => h (u * θ g * u⁻¹)) * (Ru * A) := by rw [e, mul_assoc]
  · obtain ⟨p1, -⟩ := Sh u hu h hh
    refine ⟨p1, LinearMap.ext fun y => Subtype.ext ?_⟩
    show (r (fun g => h (g * u⁻¹)) y : V) = (r h (Ru y) : V)
    obtain ⟨-, e2, -, -⟩ := (Sh u hu h hh).2.2.2 y (hY y.2)
    rw [hact _ p1, hact _ hh, b1, e2]

theorem UpperTheory.V.Z.Mult.Pi.toYdA :
    SlotBasic → LevTop → TranslF → HeckeSum → LvShift → UpperTheory.V.Z.Mult.Pi.ToYdA := by
  intro hSl hLT hTF hHS hLS E _ _ _ n S Z N hS hZ hG π u hu
  obtain ⟨hO, hC, -, hNm⟩ := hLT E n S Z N hS hZ hG
  obtain ⟨t1, t2, κ, hκ, t3⟩ := hTF E n u hu
  have hinv := (hSl E n S hS).1
  have hcont := (hSl E n S hS).2.1
  have hthe : ∀ g, thetaF E n g = (ratF E n u)⁻¹ * thF E n g * ratF E n u := by
    intro g
    rw [t1 g]
    group
  have hnorm : ∀ x, x ∈ Lev S N ↔ ratF E n u * x * (ratF E n u)⁻¹ ∈ Lev S N := by
    intro x
    rw [t3 x]
    refine ⟨hNm κ hκ x, fun hx => ?_⟩
    have := hNm κ⁻¹ ((Kf E n).inv_mem hκ) _ hx
    simpa [mul_assoc] using this
  have hθK : ∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N := by
    intro k hk
    refine (hnorm _).2 ?_
    have e : ratF E n u * thetaF E n k * (ratF E n u)⁻¹ = thF E n k := (t1 k).symm
    rw [e]
    exact (hLT E n S Z N hS hZ hG).2.2.1 k hk
  refine ⟨hθK, ?_⟩
  intro μf hμ Y ρ A hYπ hfd hne hfix hAct hsim hAA hAθ
  have hθm : ∀ a b, thetaF E n (a * b) = thetaF E n a * thetaF E n b := by
    intro a b
    simp only [hthe, map_mul]
    group
  have hθi : ∀ g, thetaF E n (thetaF E n g) = g := by
    intro g
    simp only [hthe, map_mul, map_inv, t2, hinv]
    group
  have hθu : thetaF E n (ratF E n u) = (ratF E n u)⁻¹ := by
    rw [hthe, t2]
    group
  have hθc : Continuous (thetaF E n) := by
    have : thetaF E n = fun g => (ratF E n u)⁻¹ * thF E n g * ratF E n u := funext hthe
    rw [this]
    exact (continuous_const.mul hcont).mul continuous_const
  have hv : (μf (Lev S N : Set (GF E n))).toReal ≠ 0 := by
    haveI := hμ
    exact (ENNReal.toReal_pos (hO.measure_pos μf ⟨1, (Lev S N).one_mem⟩).ne' hC.measure_lt_top.ne).ne'
  obtain ⟨v, hvdef⟩ : ∃ v : ℂ, v = (((μf (Lev S N : Set (GF E n))).toReal : ℝ) : ℂ) := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact_mod_cast hv
  have toF : ∀ {h : GF E n → ℂ}, IsHecke (Lev S N) h → IsHeckeF (Lev S N) h := fun hh =>
    ⟨hh.1, fun k₁ h₁ k₂ h₂ g => by rw [(hh.2 _ h₂ _).2, (hh.2 _ h₁ _).1]⟩
  have toH : ∀ {h : GF E n → ℂ}, IsHeckeF (Lev S N) h → IsHecke (Lev S N) h := fun hh =>
    ⟨hh.1, fun k hk x => ⟨by simpa using hh.2 k hk 1 (Lev S N).one_mem x,
      by simpa using hh.2 1 (Lev S N).one_mem k hk x⟩⟩
  have hY : Y ≤ fixed (finRep E n) (Lev S N) := fun y hy k => by
    simpa using hfix y hy k k.2
  have hact : ∀ h, IsHecke (Lev S N) h → ∀ y : Y,
      (((v⁻¹ • ρ h : Module.End ℂ Y) y : Y) : Sm E n) = Lv (finRep E n) (Lev S N) h y := by
    intro h hh y
    have e : ((ρ h y : Y) : Sm E n) = v • Lv (finRep E n) (Lev S N) h y := by
      refine Subtype.ext ?_
      have e1 := hAct h (toF hh) y
      have e2 := hHS E n (Lev S N) hO hC μf hμ h hh y (hY y.2)
      rw [e1, e2, hvdef]
      rfl
    show ((v⁻¹ • (ρ h y) : Y) : Sm E n) = _
    rw [Submodule.coe_smul, e, inv_smul_smul₀ hv0]
  obtain ⟨c1, c2, c3⟩ := core hLS (finRep E n) (Lev S N) hO hC (ratF E n u) hnorm (thetaF E n) hθc hθi hθm hθK hθu
    Y hY (fun h => v⁻¹ • ρ h) hact A hAA (fun h hh => by
      rw [mul_smul_comm, smul_mul_assoc, hAθ h (toF hh)])
  refine ⟨⟨Y, fun h => v⁻¹ • ρ h, _, hYπ, hfd, hne, hY, hact, ?_, c1, ?_⟩, v, hvdef, fun h hh =>
    ⟨toF (c3 h hh).1, ?_⟩⟩
  · intro W hW
    refine hsim W fun h hh y hy => ?_
    exact (W.smul_mem_iff (inv_ne_zero hv0)).1 (hW h (toH hh) y hy)
  · intro h hh
    have e : (fun g => h (thF E n g)) = fun g => h (ratF E n u * thetaF E n g * (ratF E n u)⁻¹) :=
      funext fun g => by rw [t1 g]
    show _ * _ = (v⁻¹ • ρ (fun g => h (thF E n g))) * _
    rw [e]
    exact c2 h hh
  · have e2 : v⁻¹ • ρ (fun g => h (g * (ratF E n u)⁻¹)) = (v⁻¹ • ρ h) *
        (v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) := (c3 h hh).2
    have key : ρ (fun g => h (g * (ratF E n u)⁻¹)) * A = v • ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [← mul_assoc, ← e2, smul_mul_assoc, smul_inv_smul₀ hv0]
    have tr : LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ Y ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [key, LinearMap.map_smul, smul_eq_mul]
    exact tr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrA
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem lv_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    Lv ρ K ((K : Set G).indicator 1) v = v := by
  have hc : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := by
    have h : (QuotientGroup.mk (QuotientGroup.mk 1 : G ⧸ K).out : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.out_eq' _
    simpa using QuotientGroup.eq.1 h
  have hq : ∀ q : G ⧸ K, q ≠ QuotientGroup.mk 1 → q.out ∉ K := by
    intro q hne hmem
    apply hne
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using hmem)
  unfold Lv levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)
    (fun q hne => by rw [Set.indicator_of_notMem (hq q hne), zero_smul]),
    Set.indicator_of_mem (show _ ∈ (K : Set G) from hc)]
  simpa using hv ⟨_, hc⟩

private theorem trOn_of_id {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    [FiniteDimensional ℂ M] (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v = v) :
    trOn M L = (Module.finrank ℂ M : ℂ) := by
  have h : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [hL v hv]; exact hv
  have hid : L.restrict h = LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, hL v.1 v.2]
  unfold trOn
  rw [dite_eq_left h, hid]
  exact LinearMap.trace_id ℂ _

private theorem finFn_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) : (fun g => finFn S φ₁ φ₂ (g, 1)) = pf S (two φ₁ φ₂) := by
  funext g
  have h1 : ∀ w : Pl E, atW w ((g, 1) : Gf E n 0) = (qw n w false g, 1) :=
    fun w => Prod.ext rfl (map_one (GeneralLinearGroup.map (pLoc E w)))
  have h2 : ∀ w : Pl E, atW w (thP E n 0 (g, 1)) = (qw n w true g, 1) := by
    intro w
    refine Prod.ext rfl ?_
    simp [atW, thP]
  unfold finFn pf
  simp only [h1, h2]
  rfl

private theorem ind_hecke {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (M N' : Subgroup (GLw n w)) (ho : IsOpen (M : Set (GLw n w))) (hM : M ≤ KGL w (n := n)) (hN : N' ≤ M) :
    IsHecke N' ((M : Set (GLw n w)).indicator 1) := by
  have hcl : IsClosed (M : Set (GLw n w)) := M.isClosed_of_isOpen ho
  have hcomp : IsCompact (M : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2.of_isClosed_subset hcl hM
  refine ⟨hcomp.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal Set.support_indicator_subset hcl), fun k hk x => ?_⟩
  have a1 : k * x ∈ M ↔ x ∈ M := M.mul_mem_cancel_left (hN hk)
  have a2 : x * k ∈ M ↔ x ∈ M := M.mul_mem_cancel_right (hN hk)
  simp only [Set.indicator, SetLike.mem_coe, a1, a2, Pi.one_apply, and_self]

theorem _root_.UpperTheory.V.Z.Mult.Pi.levelTrA : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Mult.Pi.ZTrA → UpperTheory.V.Z.Mult.Pi.SeenTrA → TTr → UpperTheory.V.Z.Mult.Pi.LevelTrA := by
  intro hAdm hZ hSeen hT E _ _ _ n S Z N hSec hSp hG π y B τ hB hτ
  obtain ⟨hne, d₀, hd₀, hd⟩ := hZ E n S Z N hSec hSp hG π y τ hτ
  let c : Pl E → ℂ := fun w => (((N w).relIndex (KGL w (n := n)) : ℕ) : ℂ) ^ 2
  have hc : ∀ w ∈ Z, ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (two φ₁ φ₂ w false) * Lv (τ w).ρ (N w) (two φ₁ φ₂ w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) :=
    fun w hw => hSeen E n w (hSp w hw).2 (τ w) (N w) (hG w).1 (hG w).2.1
  refine ⟨?_, d₀ * ∏ w ∈ Z, c w, by simp [hd₀, c], ?_⟩
  · let φ₀ : ∀ w : Pl E, LF n 0 w := fun w p => (N w : Set (GLw n w)).indicator 1 p.1
    have h2 : ∀ w b, two φ₀ φ₀ w b = (N w : Set (GLw n w)).indicator 1 := by
      intro w b
      cases b <;> rfl
    refine ⟨φ₀, fun w _ N' hN' b => ?_, Finset.prod_ne_zero_iff.2 fun w hw h0 => ?_⟩
    · rw [h2]
      exact ind_hecke w (N w) N' (hG w).1 (hG w).2.1 hN'
    · haveI : FiniteDimensional ℂ (fixed (τ w).ρ (N w)) := hAdm E n w (τ w) (N w) (hG w).1
      have e := hc w hw φ₀ φ₀ fun b => by
        rw [h2]
        exact ind_hecke w (N w) (N w) (hG w).1 (hG w).2.1 le_rfl
      rw [h0, mul_zero, h2, h2, trOn_of_id _ _ fun v hv => by
        rw [Module.End.mul_apply, lv_unit _ _ v hv, lv_unit _ _ v hv]] at e
      exact hne w hw (Submodule.finrank_eq_zero.1 (Nat.cast_eq_zero.1 e))
  · intro φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    obtain ⟨h1, h2, h3⟩ := hT E n S Z N hSec hSp hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    have hF : ∀ w ∈ Z, ∀ b, two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w b = two φ₁ φ₂ w b := by
      intro w hw b
      cases b <;> simp [two, intersection_update_fsHerm_neg_one, hw]
    have hP : ∀ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w))
        (Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w false) *
          Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) := by
      intro w hw
      rw [hF w hw, hF w hw]
      exact hc w hw φ₁ φ₂ (hφ w hw)
    rw [finFn_one S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)]
    refine ⟨h1, ?_⟩
    rw [h3, smul_mul_assoc, map_smul, hd _ h2, smul_eq_mul, Finset.prod_congr rfl hP, Finset.prod_mul_distrib]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PRankOne
section
namespace UpperTheory.V.Z.Mult.Pi

private lemma trace_idem {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (f : Module.End ℂ Y) (hf : f * f = f) (hx : ∀ x, ∃ c : ℂ, f * x * f = c • f) (h0 : f ≠ 0) :
    LinearMap.trace ℂ Y f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (LinearMap.ext h)
  have hidem : ∀ v, f (f v) = f v := fun v => by
    have := congrArg (fun g : Module.End ℂ Y => g v) hf
    simpa [Module.End.mul_apply] using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ (f y) = 1 := by
    have h1 : ¬ ∀ φ : Module.Dual ℂ Y, φ (f y) = 0 := fun h =>
      hy ((Module.forall_dual_apply_eq_zero_iff ℂ (f y)).1 h)
    push_neg at h1
    obtain ⟨ψ, hψ⟩ := h1
    refine ⟨(ψ (f y))⁻¹ • ψ, ?_⟩
    simp [hψ]
  have hr : LinearMap.range f = Submodule.span ℂ {f y} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := hx (φ.smulRight v)
      have h2 := congrArg (fun g : Module.End ℂ Y => g (f y)) hc
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hidem, hφ,
        map_smul, one_smul] at h2
      exact Submodule.mem_span_singleton.2 ⟨c, h2.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨y, rfl⟩
  have hp : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hidem v⟩
  rw [hp.trace, hr, finrank_span_singleton hy]
  simp

theorem rankOne_pf : RankOne := by
  intro Y _ _ _ f A hf hA hc hx
  by_cases h0 : f = 0
  · left
    simp [h0]
  right
  obtain ⟨c, hcA⟩ := hx A
  have hfA : f * A = c • f := by
    calc f * A = f * f * A := by rw [hf]
      _ = f * (f * A) := mul_assoc _ _ _
      _ = f * (A * f) := by rw [hc]
      _ = f * A * f := (mul_assoc _ _ _).symm
      _ = c • f := hcA
  have hsq : (c * c) • f = f := by
    calc (c * c) • f = (c • f) * (c • f) := by rw [smul_mul_smul_comm, hf]
      _ = (f * A) * (f * A) := by rw [hfA]
      _ = f * (A * f) * A := by simp only [mul_assoc]
      _ = f * (f * A) * A := by rw [hc]
      _ = (f * f) * (A * A) := by simp only [mul_assoc]
      _ = f := by rw [hf, hA, mul_one]
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • f = 0 := by rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h0
  have hn : ‖c‖ = 1 := by
    have h4 : ‖c‖ * ‖c‖ = 1 := by rw [← norm_mul, hcc, norm_one]
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1)]
  rw [hfA, map_smul, trace_idem f hf hx h0, smul_eq_mul, mul_one, hn]

end UpperTheory.V.Z.Mult.Pi
end

