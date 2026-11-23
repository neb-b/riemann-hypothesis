module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.HeckeComp
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

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.toYd_pf :
    SlotBasic → LevTop → TranslF → HeckeSum → LvShift → ToYd := by
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
  refine ⟨⟨Y, fun h => v⁻¹ • ρ h, _, hYπ, hfd, hne, hY, hact, ?_, c1, ?_⟩, v, hv0, fun h hh =>
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

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LiftRestrict
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F

private theorem lift_lift {J₀ J A : Type} [Ring A] [Algebra ℂ A] (v : J₀ → J) (e : J → A)
    (p : FreeAlgebra ℂ J₀) :
    FreeAlgebra.lift ℂ e (FreeAlgebra.lift ℂ (fun j => FreeAlgebra.ι ℂ (v j)) p) =
      FreeAlgebra.lift ℂ (fun j => e (v j)) p := by
  have h : (FreeAlgebra.lift ℂ e).comp (FreeAlgebra.lift ℂ (fun j => FreeAlgebra.ι ℂ (v j))) =
      FreeAlgebra.lift ℂ (fun j => e (v j)) := by
    apply FreeAlgebra.hom_ext
    funext j
    simp
  exact DFunLike.congr_fun h p

private theorem lift_restrict {V J : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (e : J → Module.End ℂ V) (r : J → Module.End ℂ P) (h : ∀ j (x : P), ((r j x : P) : V) = e j x)
    (p : FreeAlgebra ℂ J) : ∀ x : P, ((FreeAlgebra.lift ℂ r p x : P) : V) = FreeAlgebra.lift ℂ e p x := by
  refine FreeAlgebra.induction ℂ J (motive := fun p => ∀ x : P, ((FreeAlgebra.lift ℂ r p x : P) : V) = FreeAlgebra.lift ℂ e p x)
    ?_ ?_ ?_ ?_ p
  · intro c x
    simp [AlgHom.commutes, Module.algebraMap_end_apply]
  · intro j x
    simpa using h j x
  · intro a b ha hb x
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  · intro a b ha hb x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]

private theorem list_restrict {V ι : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (e : ι → Module.End ℂ V) (r : ι → Module.End ℂ P) (h : ∀ i (x : P), ((r i x : P) : V) = e i x)
    (l : List ι) : ∀ x : P, (((l.map r).prod x : P) : V) = (l.map e).prod x := by
  induction l with
  | nil => intro x; rfl
  | cons a l ih =>
    intro x
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, ih]

private theorem simple_of {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (W : Submodule ℂ P)
    (h : W.map P.subtype = ⊥ ∨ W.map P.subtype = P) : W = ⊥ ∨ W = ⊤ := by
  have inj := Submodule.map_injective_of_injective P.injective_subtype
  rcases h with h | h
  · left
    exact inj (by rw [h, Submodule.map_bot])
  · right
    exact inj (by rw [h, Submodule.map_subtype_top])

private theorem comm_res {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (u v : Module.End ℂ P)
    (u' v' : Module.End ℂ V) (hu : ∀ x : P, ((u x : P) : V) = u' x) (hv : ∀ x : P, ((v x : P) : V) = v' x)
    (h : Commute u' v') : Commute u v := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((u (v x) : P) : V) = ((v (u x) : P) : V)
  rw [hu, hv, hv, hu]
  exact LinearMap.congr_fun h.eq (x : V)

private theorem prod_reorder {ι A : Type} [Monoid A] (Z : Finset ι) (c : ι × Bool → A)
    (hc : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), ∀ k ∈ Z ×ˢ (Finset.univ : Finset Bool), i ≠ k → Commute (c i) (c k)) :
    ((Z ×ˢ (Finset.univ : Finset Bool)).toList.map c).prod =
      ((Finset.univ : Finset Z).toList.map fun w => c (w.1, false) * c (w.1, true)).prod := by
  classical
  have step : ∀ l : List Z, ((l.flatMap fun w => [(w.1, false), (w.1, true)]).map c).prod =
      (l.map fun w => c (w.1, false) * c (w.1, true)).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons, List.prod_cons, mul_assoc]
      rw [ih]
  have hnd : ((Finset.univ : Finset Z).toList.flatMap fun w => [(w.1, false), (w.1, true)]).Nodup := by
    refine List.nodup_flatMap.2 ⟨fun w _ => by simp, ?_⟩
    refine (Finset.nodup_toList _).imp_of_mem ?_
    intro a b _ _ hab
    simp only [Function.onFun, List.disjoint_left]
    intro x hx hx'
    apply hab
    apply Subtype.ext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simpa using h
  have hperm : (Z ×ˢ (Finset.univ : Finset Bool)).toList.Perm
      ((Finset.univ : Finset Z).toList.flatMap fun w => [(w.1, false), (w.1, true)]) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hnd).2 ?_
    rintro ⟨w, b⟩
    simp only [Finset.mem_toList, Finset.mem_product, Finset.mem_univ, and_true, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro hw
      refine ⟨⟨w, hw⟩, trivial, ?_⟩
      cases b <;> simp
    · rintro ⟨a, -, h⟩
      have hw : w = a.1 := by
        rcases h with h | h <;> exact (Prod.ext_iff.1 h).1
      rw [hw]
      exact a.2
  rw [← step]
  refine List.Perm.prod_eq' (hperm.map c) ?_
  rw [List.pairwise_map]
  refine (Finset.nodup_toList _).imp_of_mem ?_
  intro a b ha hb hab
  exact hc a (Finset.mem_toList.1 ha) b (Finset.mem_toList.1 hb) hab

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → PfHecke → ProdOp → LocComm → YLoc → ZSimple → YSwap → Isot → SimpleFix → AbsCore → ZTr := by
  intro hAdm hPf hPO hLC hYL hZS hYS hIs hSF hAC E _ _ _ n S Z N hS hZ hG π y τ hτ
  have hNo : ∀ w, IsOpen (N w : Set (GLw n w)) := fun w => (hG w).1
  have hNl : ∀ w, N w ≤ KGL w (n := n) := fun w => (hG w).2.1
  have hSl : ∀ w ∈ Z, ∀ b, Sl S (w, b) := fun w hw b => ⟨(hZ w hw).1, fun _ => (hZ w hw).2⟩
  have hZero : ∀ w, IsHecke (N w) (0 : GLw n w → ℂ) := fun w => ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hLoc := hLC E n S Z N hS hZ hG
  have hfixY : ∀ w ∈ Z, ∀ b, ∀ x ∈ y.Y, x ∈ fixed (rw' n w b) (N w) := fun w hw b x hx =>
    ((hLoc (w, b) (hSl w hw b) 0 (hZero w)).1 x (y.fix hx)).1
  have part1 : ∀ w ∈ Z, fixed (τ w).ρ (N w) ≠ ⊥ := by
    intro w hw hbot
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot y.ne
    apply hx0
    have := hIs E n π w (τ w) (hτ w hw) (N w) (hNo w) (hNl w) 1 (fun v hv => by
      rw [hbot, Submodule.mem_bot] at hv
      simp [hv]) x (y.le hx) (hfixY w hw false x hx)
    simpa using this
  haveI : FiniteDimensional ℂ y.Y := y.fd
  haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
  haveI : ∀ w : ↥Z, FiniteDimensional ℂ (fixed (τ w.1).ρ (N w.1)) := fun w =>
    hAdm E n w.1 (τ w.1) (N w.1) (hNo _)
  have hαinv : ∀ (w : ↥Z) (f : {f : GLw n w.1 → ℂ // IsHecke (N w.1) f}), ∀ x ∈ fixed (τ w.1).ρ (N w.1),
      Lv (τ w.1).ρ (N w.1) f.1 x ∈ fixed (τ w.1).ρ (N w.1) := fun w f x hx =>
    (hSF E n w.1 (τ w.1) (N w.1) (hNo _) (hNl _)).1 f.1 f.2 x hx
  have hYinv : ∀ (b : Bool) (w : ↥Z) (f : {f : GLw n w.1 → ℂ // IsHecke (N w.1) f}), ∀ x ∈ y.Y,
      Lw N w.1 b f.1 x ∈ y.Y := fun b w f x hx =>
    hYL E n S Z N hS hZ hG π y (w.1, b) (hSl w.1 w.2 b) f.1 f.2 x hx
  let α : ∀ w : ↥Z, {f : GLw n w.1 → ℂ // IsHecke (N w.1) f} → Module.End ℂ (fixed (τ w.1).ρ (N w.1)) :=
    fun w f => (Lv (τ w.1).ρ (N w.1) f.1).restrict (hαinv w f)
  let c : Bool → ∀ w : ↥Z, {f : GLw n w.1 → ℂ // IsHecke (N w.1) f} → Module.End ℂ y.Y :=
    fun b w f => (Lw N w.1 b f.1).restrict (hYinv b w f)
  have h1 : ∀ (i : ↥Z) (W : Submodule ℂ (fixed (τ i.1).ρ (N i.1))), (∀ f, ∀ x ∈ W, α i f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro w W hW
    refine simple_of _ W ((hSF E n w.1 (τ w.1) (N w.1) (hNo _) (hNl _)).2 (W.map (Submodule.subtype _))
      (Submodule.map_subtype_le _ _) ?_)
    intro f hf x hx
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    exact Submodule.mem_map.2 ⟨α w ⟨f, hf⟩ x0, hW ⟨f, hf⟩ x0 hx0, rfl⟩
  have h2 : ∀ (i : ↥Z) (p : FreeAlgebra ℂ {f : GLw n i.1 → ℂ // IsHecke (N i.1) f}),
      FreeAlgebra.lift ℂ (α i) p = 0 → FreeAlgebra.lift ℂ (c false i) p = 0 := by
    intro i p hp
    have hz : ∀ x ∈ fixed (τ i.1).ρ (N i.1), FreeAlgebra.lift ℂ (Lv (τ i.1).ρ (N i.1))
        (FreeAlgebra.lift ℂ (fun j : {f : GLw n i.1 → ℂ // IsHecke (N i.1) f} => FreeAlgebra.ι ℂ j.1) p) x = 0 := by
      intro x hx
      rw [lift_lift Subtype.val, ← lift_restrict (fixed (τ i.1).ρ (N i.1)) _ (α i) (fun _ _ => rfl) p ⟨x, hx⟩, hp]
      rfl
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h3 := hIs E n π i.1 (τ i.1) (hτ i.1 i.2) (N i.1) (hNo _) (hNl _) _ hz x.1 (y.le x.2)
      (hfixY i.1 i.2 false x.1 x.2)
    rw [lift_lift Subtype.val] at h3
    have h4 := lift_restrict y.Y (fun j : {f : GLw n i.1 → ℂ // IsHecke (N i.1) f} => Lv (rw' n i.1 false) (N i.1) j.1)
      (c false i) (fun _ _ => rfl) p x
    rw [h3] at h4
    simpa using h4
  have h3 : ∀ (i k : ↥Z), i ≠ k → ∀ f g, Commute (c false i f) (c false k g) := by
    intro i k hik f g
    refine comm_res y.Y _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      ((hLoc (i.1, false) (hSl _ i.2 _) f.1 f.2).2 (k.1, false) (hSl _ k.2 _) ?_ g.1 g.2)
    intro h
    exact hik (Subtype.ext (Prod.ext_iff.1 h).1)
  have h4 : ∀ (i k : ↥Z) f g, Commute (c false i f) (c true k g) := by
    intro i k f g
    refine comm_res y.Y _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      ((hLoc (i.1, false) (hSl _ i.2 _) f.1 f.2).2 (k.1, true) (hSl _ k.2 _) (by simp) g.1 g.2)
  have h5 : ∀ (i : ↥Z) f, y.A * c false i f = c true i f * y.A := by
    intro i f
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hYS E n S Z N hS hZ hG π y i.1 i.2 f.1 f.2 x (c false i f x) rfl
  have h6 : ∀ W : Submodule ℂ y.Y, (∀ (i : ↥Z) f, ∀ x ∈ W, c false i f x ∈ W ∧ c true i f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine simple_of _ W (hZS E n S Z N hS hZ hG π y (W.map (Submodule.subtype _))
      (Submodule.map_subtype_le _ _) ?_)
    intro w hw b f hf x hx
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    have := hW ⟨w, hw⟩ ⟨f, hf⟩ x0 hx0
    cases b
    · exact Submodule.mem_map.2 ⟨_, this.1, rfl⟩
    · exact Submodule.mem_map.2 ⟨_, this.2, rfl⟩
  obtain ⟨d, hd, key⟩ := hAC ↥Z (fun w : ↥Z => {f : GLw n w.1 → ℂ // IsHecke (N w.1) f})
    (fun w : ↥Z => ↥(fixed (τ w.1).ρ (N w.1))) y.Y α (c false) (c true) y.A h1 h2 h3 h4 y.sq h5 h6
  refine ⟨part1, d, hd, fun F hF => ?_⟩
  have hFh : ∀ w (_ : w ∈ Z) b, IsHecke (N w) (F w b) := fun w hw b =>
    (hF.1 (w, b) (by simp [hw])).2
  have hpf := hPf E n S Z N hS hZ hG _ F hF
  have hcomm : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), ∀ k ∈ Z ×ˢ (Finset.univ : Finset Bool), i ≠ k →
      Commute (Lw N i.1 i.2 (F i.1 i.2)) (Lw N k.1 k.2 (F k.1 k.2)) := by
    intro i hi k hk hik
    exact (hLoc i (hF.1 i hi).1 _ (hF.1 i hi).2).2 k (hF.1 k hk).1 hik _ (hF.1 k hk).2
  have e1 : y.r (pf S F) = (((Finset.univ : Finset ↥Z).toList.map fun i =>
      c false i ⟨F i.1 false, hFh _ i.2 _⟩ * c true i ⟨F i.1 true, hFh _ i.2 _⟩).prod) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [y.act _ hpf x, hPO E n S Z N hS hZ hG _ F hF x (y.fix x.2),
      prod_reorder Z (fun i => Lw N i.1 i.2 (F i.1 i.2)) hcomm]
    exact (list_restrict y.Y _ _ (fun _ _ => rfl) _ x).symm
  rw [e1, key (fun i => ⟨F i.1 false, hFh _ i.2 _⟩) (fun i => ⟨F i.1 true, hFh _ i.2 _⟩)]
  congr 1
  rw [← Finset.prod_coe_sort Z]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hinv : ∀ v ∈ fixed (τ w.1).ρ (N w.1), (Lv (τ w.1).ρ (N w.1) (F w.1 false) * Lv (τ w.1).ρ (N w.1) (F w.1 true)) v ∈
      fixed (τ w.1).ρ (N w.1) := fun v hv =>
    hαinv w ⟨_, hFh _ w.2 _⟩ _ (hαinv w ⟨_, hFh _ w.2 _⟩ v hv)
  rw [GlobalTheory.BCT.trOn, dite_eq_left hinv]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLevTop
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.levTop_pf :
    SlotBasic → LevTop := by
  intro hS E _ _ _ n S Z N hSec hZ hG
  obtain ⟨hinv, -, hloc, -, -, hinert, hK⟩ := hS E n S hSec
  have mem : ∀ (M : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (x : GF E n),
      x ∈ Lev S M ↔ ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
    intro M x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hKq : ∀ k ∈ PositivityTheory.Rg.BcB.G8.Kf E n, ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i →
      qw n i.1 i.2 k ∈ GlobalTheory.LFun.KGL i.1 (n := n) := fun k hk => (mem _ k).1 ((hK k).2 hk)
  have hsub : (Lev S N : Set (GF E n)) ⊆ (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) := by
    intro x hx
    exact (hK x).1 ((mem _ x).2 fun i hi => (hG i.1).2.1 ((mem N x).1 hx i hi))
  have hset : (Lev S N : Set (GF E n)) = (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) ∩
      ⋂ i ∈ {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i},
        (qw n i.1 i.2) ⁻¹' (N i.1 : Set (GlobalTheory.BCT.GLw n i.1)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hsub hx, ?_⟩
      simp only [Set.mem_iInter]
      exact fun i hi => (mem N x).1 hx i hi.2
    · rintro ⟨hx, hx'⟩
      simp only [Set.mem_iInter] at hx'
      refine (mem N x).2 fun i hi => ?_
      by_cases hz : i.1 ∈ Z
      · exact hx' i ⟨hz, hi⟩
      · rw [(hG i.1).2.2.2 hz]
        exact hKq x hx i hi
  have hfinZ : {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i}.Finite :=
    ((Z.finite_toSet).prod (Set.finite_univ (α := Bool))).subset fun i hi => ⟨hi.1, trivial⟩
  have hopen : IsOpen (Lev S N : Set (GF E n)) := by
    rw [hset]
    refine GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.inter (hfinZ.isOpen_biInter fun i _ => ?_)
    exact ((hG i.1).1).preimage (hloc i.1 i.2).2.1
  refine ⟨hopen, ?_, ?_, ?_⟩
  · exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Lev S N) hopen) hsub
  · intro k hk
    have hq0 : ∀ w, qw n w false (GlobalTheory.BCT.thF E n k) = qw n w true k := fun w => rfl
    have hq1 : ∀ w, qw n w true (GlobalTheory.BCT.thF E n k) = qw n w false k := by
      intro w
      change qw n w false (GlobalTheory.BCT.thF E n (GlobalTheory.BCT.thF E n k)) = _
      rw [hinv]
    refine (mem N _).2 ?_
    rintro ⟨w, b⟩ ⟨hw, hb⟩
    cases b with
    | true =>
      exact (hq1 w).symm ▸ (mem N k).1 hk (w, false) ⟨hw, by simp⟩
    | false =>
      change qw n w false (GlobalTheory.BCT.thF E n k) ∈ N w
      rw [hq0]
      by_cases hs : GlobalTheory.UnitaryBC.IsSplitAt w
      · exact (mem N k).1 hk (w, true) ⟨hw, fun _ => hs⟩
      · have hz : w ∉ Z := fun h => hs (hZ w h).2
        have h0 : qw n w false k ∈ N w := (mem N k).1 hk (w, false) ⟨hw, by simp⟩
        rw [(hG w).2.2.2 hz] at h0 ⊢
        exact (hinert w hs k).2 h0
  · intro k hk x hx
    refine (mem N _).2 fun i hi => ?_
    rw [map_mul, map_mul, map_inv]
    exact (hG i.1).2.2.1 _ (hKq k hk i hi) _ ((mem N x).1 hx i hi)
end

