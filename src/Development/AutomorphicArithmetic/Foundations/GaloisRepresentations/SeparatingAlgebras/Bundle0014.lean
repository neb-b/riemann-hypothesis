module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0308
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CharSum
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.charSum_pf :
    UpperTheory.Gal.Gen.CharSum := by
  intro N _
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN⟩
  have hz0 : ζ ≠ 0 := hζ.ne_zero hN
  let u : ℂˣ := Units.mk0 ζ hz0
  have huN : u ^ N = 1 := by
    ext
    simp [u, hζ.pow_eq_one]
  have hu : ∀ j : ℕ, (u ^ j) ^ N = 1 := by
    intro j
    rw [← pow_mul, mul_comm, pow_mul, huN, one_pow]
  let χ : Fin N → (Multiplicative (ZMod N) →* ℂˣ) := fun j => GlobalTheory.CongSc.zchar (u ^ (j : ℕ)) (hu j)
  have hval : ∀ (j : Fin N) (x : Multiplicative (ZMod N)),
      ((χ j x : ℂˣ) : ℂ) = (ζ ^ (j : ℕ)) ^ (Multiplicative.toAdd x).val := by
    intro j x
    simp [χ, GlobalTheory.CongSc.zchar_apply, u]
  have hone : ∀ j : Fin N, j ≠ 0 → ((χ j (Multiplicative.ofAdd 1) : ℂˣ) : ℂ) = ζ ^ (j : ℕ) := by
    intro j hj
    rw [hval]
    have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    have h1 : 1 < N := by
      have := j.isLt
      omega
    rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
  refine ⟨(Finset.univ.erase 0).image χ, ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    intro h
    have h2 : ζ ^ (j : ℕ) = 1 := by
      rw [← hone j hj0, h]
      simp
    have hd := (hζ.pow_eq_one_iff_dvd (j : ℕ)).mp h2
    exact hj0 (Fin.ext (Nat.eq_zero_of_dvd_of_lt hd j.isLt))
  · intro x
    rw [Finset.sum_image (by
      intro j hj k hk hjk
      have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
      have h3 := hone j hj0
      rw [hjk, hone k hk0] at h3
      exact (Fin.ext (hζ.pow_inj k.isLt j.isLt h3)).symm)]
    simp_rw [hval]
    have key := GlobalTheory.CongSc.sum_roots hζ (Multiplicative.toAdd x).val (ZMod.val_lt _)
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin N))] at key
    simp only [Fin.val_zero, pow_zero, one_pow] at key
    split_ifs at key
    · exact Or.inr key
    · exact Or.inl key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LevelEx
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.levelEx_pf :
    UpperTheory.Gal.Gen.LevelEx := by
  intro E _ _ _ a W f
  obtain ⟨K0, hK0o, hK0c⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E a
  let C : Subgroup (UA E a) := K0.map (finU (E := E) (n := a)).subtype
  have hCf : C ≤ finU (E := E) (n := a) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hCc : IsCompact (C : Set (UA E a)) := by
    have h := hK0c.image (continuous_subtype_val (p := fun x => x ∈ finU (E := E) (n := a)))
    exact h
  have hCo : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU (E := E) (n := a) ⊆ C := by
    obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hK0o
    refine ⟨t, ht, ?_, ?_⟩
    · have h1 : (1 : finU (E := E) (n := a)) ∈ (K0 : Set (finU (E := E) (n := a))) := K0.one_mem
      rw [← hte] at h1
      exact h1
    · rintro x ⟨hxt, hxf⟩
      have hx : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ (K0 : Set (finU (E := E) (n := a))) := by
        rw [← hte]
        exact hxt
      exact ⟨⟨x, hxf⟩, hx, rfl⟩
  obtain ⟨hc, N, hN, h1, hNC⟩ := GlobalTheory.CongSc.stab_level W f C hCf hCc hCo
  exact ⟨C ⊓ GlobalTheory.CongSc.stab W f, ⟨inf_le_left.trans hCf, hc, N, hN, h1, hNC⟩, fun k hk v g => hk.2 v g⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ToPolyX
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.toPolyX_pf :
    UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.ToPolyX := by
  intro hPF E _ _ _ l _ ι a w₀ K hK lam P hD Jx t η hFr hact U hU ε hε
  classical
  obtain ⟨W, f, hW, hf0, hfU, hfK, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K U hK hU w₀
  have hWe : Wt.ofFam lam = W := funext fun v => by
    show lam v.embedding = W v
    rw [← hW, Wt.at_embedding]
  rw [hWe] at hD hFr
  obtain ⟨X, b, hbd, hdef, hne⟩ := hFr
  obtain ⟨g₀, i₀, hz⟩ : ∃ g i, f.1 (b g i) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (hdef f h)
  set z₀ := f.1 (b g₀ i₀) g₀ with hz₀
  let f₁ : algForms W := z₀⁻¹ • f
  have hf₁ : ∀ v g, f₁.1 v g = z₀⁻¹ * f.1 v g := fun v g => rfl
  have hf₁K : f₁ ∈ fixedBy W K := fun k hk v g => by rw [hf₁, hf₁, hfK k hk v g]
  have hf₁U : ∀ v, f₁.1 v ∈ U := fun v => U.smul_mem _ (hfU v)
  obtain ⟨R₀, hR₀⟩ := hbd f₁
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : ∀ g i, ‖ι.symm (f₁.1 (b g i) g)‖ ≤ R := fun g i => (hR₀ g i).trans (le_max_left _ _)
  obtain ⟨G, hG, e, he, hfe⟩ := hD f₁ hf₁K (ε / R) (div_pos hε hRpos)
  obtain ⟨I, F, hI, hsum⟩ := (hPF E a W K P).2.2.2.2 G hG
  let T : Jx → Module.End ℂ (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun j =>
    LinearMap.llcomp ℂ W.Sp (UA E a → ℂ) (UA E a → ℂ) (GlobalTheory.CongSc.opL (t j))
  let ev : UA E a × X → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) →ₗ[ℂ] ℂ := fun x =>
    (LinearMap.proj x.1) ∘ₗ (LinearMap.applyₗ (b x.1 x.2))
  have hT : ∀ j (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v, T j F' v = opOf (RU E a) (t j) (F' v) := fun _ _ _ => rfl
  have hev : ∀ x (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)), ev x F' = F' (b x.1 x.2) x.1 := fun _ _ => rfl
  have hne' : ∀ (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R' : ℝ), (∀ x, ‖ι.symm (ev x F')‖ ≤ R') →
      ∀ j x, ‖ι.symm (ev x (T j F'))‖ ≤ R' := fun F' R' hR' j x =>
    hne F' R' (fun g i => hR' (g, i)) j x.1 x.2
  have heig0 : ∀ j, T j f₁.1 = η U j • f₁.1 := by
    intro j; apply LinearMap.ext; intro v
    rw [hT, LinearMap.smul_apply]
    exact hact U hU.aut (f₁.1 v) (hf₁U v) (fun x hx => funext fun g => hf₁K x hx v g) j
  have hnorm : ‖ι.symm (ev (g₀, i₀) f₁.1)‖ = 1 := by
    have : ev (g₀, i₀) f₁.1 = 1 := by
      rw [hev]
      show z₀⁻¹ * f.1 (b g₀ i₀) g₀ = 1
      exact inv_mul_cancel₀ hz
    rw [this, map_one, norm_one]
  let vv : ↥I → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun π => -(F π.1).1
  let η' : ↥I → Jx → ℂ := fun π => η π.1.V
  have heig : ∀ π j, T j (vv π) = η' π j • vv π := by
    rintro ⟨π, hπ⟩ j
    obtain ⟨-, hfin, hfix, -⟩ := hI π hπ
    have h : T j (F π).1 = η π.V j • (F π).1 := by
      apply LinearMap.ext; intro v
      rw [hT, LinearMap.smul_apply]
      exact hact π.V π.isAut _ (AutSub.mem_finPart.1 hfin v)
        (fun x hx => funext fun g => hfix x hx v g) j
    show T j (-(F π).1) = η π.V j • -(F π).1
    rw [map_neg, h, smul_neg]
  have hvsum : f₁.1 + ∑ π, vv π = f₁.1 - G.1 := by
    have h1 : ∑ π, vv π = -G.1 := by
      simp only [vv]
      rw [Finset.sum_neg_distrib, Finset.sum_coe_sort I (fun π => (F π).1), hsum, Submodule.coe_sum]
    rw [h1, sub_eq_add_neg]
  have hbound : ∀ x, ‖ι.symm (ev x (f₁.1 + ∑ π, vv π))‖ ≤ ε := by
    intro x
    have h1 : ev x (f₁.1 + ∑ π, vv π) = e x.1 * f₁.1 (b x.1 x.2) x.1 := by
      rw [hvsum, hev]
      exact hfe _ _
    rw [h1, map_mul, norm_mul]
    calc ‖ι.symm (e x.1)‖ * ‖ι.symm (f₁.1 (b x.1 x.2) x.1)‖ ≤ ε / R * R :=
          mul_le_mul (he _) (hR _ _) (norm_nonneg _) (div_pos hε hRpos).le
      _ = ε := div_mul_cancel₀ _ hRpos.ne'
  obtain ⟨s, c, hs, hP⟩ := GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality l ι (W.Sp →ₗ[ℂ] (UA E a → ℂ)) (UA E a × X) Jx
    ↥I T ev hne' f₁.1 (η U) (g₀, i₀) heig0 hnorm vv η' heig ε hbound
  refine ⟨s, c, ?_, hP⟩
  intro z hz'
  obtain ⟨⟨π, hπ⟩, rfl⟩ := hs z hz'
  obtain ⟨hPπ, hfin, hfix, hF0⟩ := hI π hπ
  refine ⟨π.V, ?_, hPπ, rfl⟩
  have h := GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form E a π W K (F π) hfin hF0 (fun k hk v g => hfix k hk v g)
  have hl' : (fun τ => W.at τ) = lam := funext hW
  rwa [hl'] at h
end

