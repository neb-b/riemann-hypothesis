module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

theorem UpperTheory.V.Z.Ord.ordJac :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → OrdJac := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ _ v hv hv0 a ha
  obtain ⟨hker, hsm, -, -, -, -, -, hidx, hz, -⟩ := glBridge k n V π
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hp : ∀ t w, jacB π t (p w) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) w) :=
    fun t w => UnramFixed.jacB_apply π t _
  have hlist : ∀ s : List ℕ, (∀ j ∈ s, j < n) → (s.map (al k n)).prod ∈ (glIwa k n).P ∧
      ∃ b : ℂ, b ≠ 0 ∧ (glIwa k n).uOp π (s.map (al k n)).prod v = b • v := by
    intro s
    induction s with
    | nil =>
      exact fun _ => ⟨one_mem _, 1, one_ne_zero, by
        simpa using (uOpMul _ (glIwa k n) ℂ V π 1 1 (one_mem _) (one_mem _) v hv.1).2.2.1⟩
    | cons j s ih =>
      intro hs
      obtain ⟨hP, b, hb, h2⟩ := ih fun i hi => hs i (List.mem_cons_of_mem _ hi)
      rw [List.map_cons, List.prod_cons]
      refine ⟨mul_mem (al_mem k n j) hP, ?_⟩
      rcases j with _ | j
      · have e : al k n 0 = 1 := by
          rw [al, upow, ← (diagT k (Fin n)).map_one]; congr 1; funext i; simp
        rw [e, one_mul]
        exact ⟨b, hb, h2⟩
      · have hj := ha ⟨j, by have := hs _ List.mem_cons_self; omega⟩
        refine ⟨a (j + 1) * b, mul_ne_zero hj.1 hb, ?_⟩
        rw [← (uOpMul _ (glIwa k n) ℂ V π _ _ (al_mem k n _) hP v hv.1).2.1, h2, map_smul]
        have e := hj.2
        simp only at e
        rw [e, smul_smul, mul_comm]
  obtain ⟨-, b, hb, hzb⟩ := hlist (List.range n) fun j hj => List.mem_range.1 hj
  rw [← hz] at hzb
  have hpow : ∀ j : ℕ, ((glIwa k n).uOp π (glIwa k n).z ^ j) v = b ^ j • v := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hzb, smul_smul, pow_succ]
  have hx0 : p v ≠ 0 := by
    intro h
    have h0 : v ∈ (glIwa k n).jacKer π := hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨j, hj⟩ := (propCker _ (glIwa k n) ℂ V π (hsm hπ) v hv.1).1 h0
    rw [hpow] at hj
    exact hv0 ((smul_eq_zero.1 hj).resolve_left (pow_ne_zero j hb))
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  have := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  have existsForm : ∀ {G W : Type} [CommGroup G] [TopologicalSpace G]
        [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G] [AddCommGroup W] [Module ℂ W]
        {ρ : Representation ℂ G W} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
      {x : W} (hx : x ≠ 0), ∃ μ : G →* ℂˣ, IsSmoothChar μ ∧ (∀ (t : G) (c : ℂ), ρ t x = c • x → (μ t : ℂ) = c) ∧
        ∃ l : W →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := by
    intro G W _ _ _ _ _ _ ρ hρ hl x hx
    have powComm : ∀ (t g : G) (c : ℂ) (m : ℕ) (v : W),
        ((ρ t - c • (1 : Module.End ℂ W)) ^ m) (ρ g v) = ρ g (((ρ t - c • (1 : Module.End ℂ W)) ^ m) v) := by
      intro t g c m v
      have hc : Commute (ρ t) (ρ g) := by
        show ρ t * ρ g = ρ g * ρ t
        rw [← map_mul, ← map_mul, mul_comm]
      have h2 : Commute (ρ t - c • (1 : Module.End ℂ W)) (ρ g) :=
        hc.sub_left ((Commute.one_left _).smul_left c)
      exact LinearMap.congr_fun ((h2.pow_left m).eq) v

    have powMem : ∀ (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
        (v : W) (hv : v ∈ N.toSubmodule), ((ρ t - c • (1 : Module.End ℂ W)) ^ m) v ∈ N.toSubmodule := by
      intro N t c m v hv
      induction m with
      | zero => simpa using hv
      | succ m ih =>
        rw [pow_succ', mul_apply_eq_comp]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self]
        exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)

    have existsNil : ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧
        ∀ (t : G) (c : ℂ), ρ t x = c • x → ∃ m : ℕ, ∀ v, ((ρ t - c • (1 : Module.End ℂ W)) ^ m) v ∈ N.toSubmodule := by
      have hwf := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
      obtain ⟨N, hxN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min
        {N | x ∉ N.toSubmodule} ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
      have hxN' : x ∉ N.toSubmodule := hxN
      refine ⟨N, fun h => hxN' (by rw [h]; exact Submodule.mem_top), fun t c hx1 => ?_⟩
      obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ W, E = ρ t - c • (1 : Module.End ℂ W) := ⟨_, rfl⟩
      have hc : ∀ m g w, (E ^ m) (ρ g w) = ρ g ((E ^ m) w) := by
        subst hE
        exact fun m g w => powComm t g c m w
      have hm : ∀ m w, w ∈ N.toSubmodule → (E ^ m) w ∈ N.toSubmodule := by
        subst hE
        exact fun m w hw => powMem N t c m w hw
      have hEx : E x = 0 := by
        rw [hE, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, hx1, sub_self]
      rw [← hE]
      let M : ℕ →o Subrepresentation ρ :=
        ⟨fun j => ⟨N.toSubmodule.comap (E ^ j), fun g v hv => by
          show (E ^ j) (ρ g v) ∈ N.toSubmodule
          rw [hc]
          exact N.apply_mem_toSubmodule g hv⟩, fun i j hij v hv => by
          show (E ^ j) v ∈ N.toSubmodule
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
          rw [add_comm, pow_add, mul_apply_eq_comp]
          exact hm d _ hv⟩
      obtain ⟨J, hJ⟩ := WellFoundedGT.monotone_chain_condition M
      refine ⟨J + 1, fun v => ?_⟩
      by_contra hv
      let L : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (E ^ (J + 1)), fun g w hw => by
        obtain ⟨n, hn, y, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
        rw [map_add (f := _), ← hc]
        exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hn) ⟨ρ g u, rfl⟩⟩
      have hlt : N < L := lt_of_le_of_ne (le_sup_left : N.toSubmodule ≤ _) (fun h => hv (by
        have h5 : (E ^ (J + 1)) v ∈ L.toSubmodule := Submodule.mem_sup_right ⟨v, rfl⟩
        rw [← h] at h5
        exact h5))
      have hxL : x ∈ L.toSubmodule := by
        by_contra hxL
        exact hmax L hxL hlt
      obtain ⟨n, hn, y, ⟨u, rfl⟩, hxe⟩ := Submodule.mem_sup.1 hxL
      have h1 : (E ^ (J + 1)) x = 0 := by
        rw [pow_succ, mul_apply_eq_comp, hEx, map_zero]
      have h2 : (E ^ (J + 1)) ((E ^ (J + 1)) u) ∈ N.toSubmodule := by
        have h6 := congrArg (E ^ (J + 1)) hxe
        rw [map_add (f := _), h1] at h6
        rw [eq_neg_of_add_eq_zero_right h6]
        exact N.toSubmodule.neg_mem (hm _ n hn)
      have h3 : u ∈ (M (2 * J + 2)).toSubmodule := by
        show (E ^ (2 * J + 2)) u ∈ N.toSubmodule
        rw [show 2 * J + 2 = (J + 1) + (J + 1) by omega, pow_add, mul_apply_eq_comp]
        exact h2
      rw [← hJ (2 * J + 2) (by omega)] at h3
      change (E ^ J) u ∈ N.toSubmodule at h3
      have h4 : (E ^ (J + 1)) u ∈ N.toSubmodule := by
        rw [pow_succ', mul_apply_eq_comp]
        simpa using hm 1 _ h3
      exact hxN' (hxe ▸ N.toSubmodule.add_mem hn h4)
    obtain ⟨N, hNtop, hnil⟩ := existsNil
    have hwf := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
    obtain ⟨P, ⟨hNP, hPtop⟩, hPmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min
      {P | N ≤ P ∧ P ≠ ⊤} ⟨N, le_rfl, hNtop⟩
    have hcov : P ⋖ ⊤ := covBy_iff_lt_and_eq_or_eq.2 ⟨lt_top_iff_ne_top.2 hPtop, fun c hPc _ => by
      by_cases hc : c = ⊤
      · exact Or.inr hc
      · exact Or.inl (by_contra fun hne => hPmax c ⟨hNP.trans hPc, hc⟩ (lt_of_le_of_ne hPc (Ne.symm hne)))⟩
    have hirr := isIrreducible_subQuot hcov
    have hsub : IsSubquotient (subQuot ⊤ P) ρ :=
      ⟨⊤, ⟨Submodule.mkQ _, fun g => LinearMap.ext fun w => rfl⟩, Submodule.mkQ_surjective _⟩
    have hsm := hsub.isSmooth hρ
    obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hsm hirr
    let π0 : W →ₗ[ℂ] (↥(⊤ : Subrepresentation ρ).toSubmodule ⧸
        Submodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype P.toSubmodule) :=
      (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict _ LinearMap.id fun v => Submodule.mem_top)
    have hπ0 : ∀ g v, π0 (ρ g v) = (μ g : ℂ) • π0 v := fun g v => by
      rw [← hμ]
      rfl
    have hz : ∀ v, π0 v = 0 ↔ v ∈ P.toSubmodule := fun v => by
      show Submodule.Quotient.mk (⟨v, Submodule.mem_top⟩ : ↥(⊤ : Subrepresentation ρ).toSubmodule) = 0 ↔ _
      exact Submodule.Quotient.mk_eq_zero _
    obtain ⟨v0, hv0⟩ : ∃ v, v ∉ P.toSubmodule := by
      by_contra hall
      push Not at hall
      exact hPtop (Subrepresentation.ext (eq_top_iff.2 fun v _ => hall v))
    have hq0 : π0 v0 ≠ 0 := fun h => hv0 ((hz v0).1 h)
    have hpow : ∀ (t : G) (c : ℂ) (m : ℕ) (v : W),
        π0 (((ρ t - c • (1 : Module.End ℂ W)) ^ m) v) = (((μ t : ℂ) - c) ^ m) • π0 v := by
      intro t c m
      induction m with
      | zero => intro v; simp
      | succ m ih =>
        intro v
        rw [pow_succ', mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.smul_apply,
          one_apply_eq_self, map_sub, map_smul, hπ0, ih, pow_succ', mul_smul, sub_smul]
    refine ⟨μ, ?_, ?_, ?_⟩
    · have hker : (μ.ker : Set G) = {g | subQuot ⊤ P g (π0 v0) = π0 v0} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_ofPred_eq, hμ]
        constructor
        · intro h
          rw [h]
          simp
        · intro h
          have h7 : ((μ g : ℂ) - 1) • π0 v0 = 0 := by rw [sub_smul, h, one_smul, sub_self]
          rcases smul_eq_zero.1 h7 with h' | h'
          · exact Units.ext (by simpa [sub_eq_zero] using h')
          · exact absurd h' hq0
      show IsOpen (μ.ker : Set G)
      rw [hker]
      exact hsm _
    · intro t c htc
      obtain ⟨m, hm⟩ := hnil t c htc
      have h8 := hpow t c m v0
      rw [(hz _).2 (hNP (hm v0))] at h8
      rcases smul_eq_zero.1 h8.symm with h' | h'
      · exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h').1
      · exact absurd h' hq0
    · obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ _, φ (π0 v0) ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hq0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
      refine ⟨φ ∘ₗ π0, fun h => hφ (by simpa using LinearMap.congr_fun h v0), fun g v => ?_⟩
      simp only [LinearMap.comp_apply, hπ0, map_smul, smul_eq_mul]
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := existsForm (isSmooth_jacB hπ) hl hx0
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    have h1 : jacB π (Pi.mulSingle i (u : kˣ)) (p v) = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • p v := by
      rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
      exact congrArg p (hv.2.2 (eT k n i u))
    have ht : torusChar ψ (Pi.mulSingle i (u : kˣ)) = ψ i u := by
      rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one])
        (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same]
    rw [← ht]
    exact Units.ext (hμ _ _ h1)
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  have hnum : ∀ (ω : Fin n → kˣ →* ℂˣ) {j : ℕ}, j ≤ n →
      ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) *
        ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
          (torusChar (fun i => ω i * absPow k (((n : ℂ) - 1) / 2))
            (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = psEig ω j := by
    intro ω j hj
    have hQ0 : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have harg : (Nat.card 𝓀[k] : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_pos.ne
    have hu : ∀ s : ℂ, ((absPow k s (unif k) : ℂˣ) : ℂ) = ((Nat.card 𝓀[k] : ℂ) ^ s)⁻¹ := by
      intro s
      rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one UpperTheory.V.Hi.GlAx.unif_spec]
      simp only [zpow_neg, zpow_one, Complex.ofReal_inv, Complex.ofReal_natCast, resCard]
      exact Complex.inv_cpow _ _ harg
    have he : ∀ (s : ℂ) (i : Fin n), ((absPow k s (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂˣ) : ℂ)
        = if (i : ℕ) < j then ((Nat.card 𝓀[k] : ℂ) ^ s)⁻¹ else 1 := by
      intro s i
      split_ifs <;> simp [hu]
    have hω : ∀ i : Fin n, ((ω i (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂˣ) : ℂ)
        = if (i : ℕ) < j then ((ω i (unif k) : ℂˣ) : ℂ) else 1 := by
      intro i
      split_ifs <;> simp
    have hdet : ∀ (t : Fin n → kˣ) (i : Fin n),
        Matrix.GeneralLinearGroup.det ((leviTorus k (Fin n) t) i) = t i := fun t i => by
      have h := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i
      exact h
    have alg : ∀ (a b w : ℂ) (i : ℕ), i < n → a + b = (n : ℂ) - 1 - (i : ℂ) →
        ((Nat.card 𝓀[k] : ℂ) ^ a)⁻¹ * (w * ((Nat.card 𝓀[k] : ℂ) ^ b)⁻¹)
          = w * ((Nat.card 𝓀[k] : ℂ) ^ i / (Nat.card 𝓀[k] : ℂ) ^ (n - 1)) := by
      intro a b w i hi hab
      have h1 : (Nat.card 𝓀[k] : ℂ) ^ a * (Nat.card 𝓀[k] : ℂ) ^ b
          = (Nat.card 𝓀[k] : ℂ) ^ (n - 1) / (Nat.card 𝓀[k] : ℂ) ^ i := by
        rw [← Complex.cpow_add _ _ hQ0, hab, Complex.cpow_sub _ _ hQ0, Complex.cpow_natCast,
          ← Complex.cpow_natCast _ (n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [show ((Nat.card 𝓀[k] : ℂ) ^ a)⁻¹ * (w * ((Nat.card 𝓀[k] : ℂ) ^ b)⁻¹)
          = w * ((Nat.card 𝓀[k] : ℂ) ^ a * (Nat.card 𝓀[k] : ℂ) ^ b)⁻¹ by ring, h1, inv_div]
    have hsum : ∀ f : ℕ → ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), f i
        = ∑ i ∈ Finset.range j, f i := by
      intro f
      rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < j then f i else 0) n]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [Finset.sum_range_add, Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.1 hi)),
        Finset.sum_eq_zero (fun x _ => ite_eq_right (by omega)), add_zero]
    have hsumid : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), (i : ℕ)
        = ∑ i ∈ Finset.range j, i := hsum (fun i => i)
    have hcard : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).card = j := by
      rw [Finset.card_eq_sum_ones, hsum (fun _ => 1)]
      simp
    have hexp : j * (n - j) + (∑ i ∈ Finset.range j, i) + (∑ i ∈ Finset.range j, i) = (n - 1) * j := by
      have h2 := Finset.sum_range_id_mul_two j
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rcases j with _ | j
      · simp
      · rw [show j + 1 + d - (j + 1) = d by omega, show j + 1 + d - 1 = j + d by omega] at *
        rw [show j + 1 - 1 = j by omega] at h2
        nlinarith [h2]
    rw [deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod]
    simp only [hdet, modExp_fin _ (fun _ => Fintype.card_unit), MonoidHom.mul_apply, Units.val_mul, he, hω]
    rw [← Finset.prod_mul_distrib]
    have hprod : (∏ x : Fin n, (if (x : ℕ) < j then ((Nat.card 𝓀[k] : ℂ) ^
          ((((n : ℤ) - 1 - 2 * ((x : ℕ) : ℤ) : ℤ) : ℂ) / 2))⁻¹ else 1) *
          ((if (x : ℕ) < j then ((ω x (unif k) : ℂˣ) : ℂ) else 1) *
            if (x : ℕ) < j then ((Nat.card 𝓀[k] : ℂ) ^ (((n : ℂ) - 1) / 2))⁻¹ else 1))
        = ∏ x : Fin n, if (x : ℕ) < j then ((ω x (unif k) : ℂˣ) : ℂ) *
            ((Nat.card 𝓀[k] : ℂ) ^ (x : ℕ) / (Nat.card 𝓀[k] : ℂ) ^ (n - 1)) else 1 :=
      Finset.prod_congr rfl fun x _ => by
        split_ifs with h
        · exact alg _ _ _ x x.isLt (by push_cast; ring)
        · simp
    rw [hprod, ← Finset.prod_filter]
    unfold psEig
    rw [Nat.cast_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_div_distrib,
      Finset.prod_inv_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hcard, hsumid]
    rw [show ((Nat.card 𝓀[k] : ℂ) ^ (n - 1)) ^ j = (Nat.card 𝓀[k] : ℂ) ^ (j * (n - j)) *
        (Nat.card 𝓀[k] : ℂ) ^ (∑ i ∈ Finset.range j, i) * (Nat.card 𝓀[k] : ℂ) ^ (∑ i ∈ Finset.range j, i) by
      rw [← pow_mul, ← pow_add, ← pow_add, hexp]]
    field_simp
  refine ⟨ω, hω, hinv, hsq, fun j => ?_⟩
  have hm : (j : ℕ) + 1 ≤ n := j.2
  have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n ((j : ℕ) + 1)) v hv.1
  rw [hker, hidx _ hm] at h1
  have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
  rw [map_sub, map_smul, sub_eq_zero, (ha j).2, map_smul] at h2
  have hQ : ((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ Nat.card_pos.ne')
  have h3 := hμ (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))
    ((((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n)
      (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))))⁻¹ : ℂˣ) : ℂ) *
      (((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ)⁻¹ * a ((j : ℕ) + 1))) (by
    rw [hp, mul_smul]
    congr 1
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hQ, one_smul]
    rfl)
  have key : ∀ (Q x : ℂ) (d : ℂˣ), Q ≠ 0 → Q * ((d : ℂ) * (((d⁻¹ : ℂˣ) : ℂ) * (Q⁻¹ * x))) = x := fun Q x d h => by
    rw [Units.val_inv_eq_inv_val]
    have := d.ne_zero
    field_simp
  rw [← hnum ω hm, h3]
  exact key _ _ _ hQ
