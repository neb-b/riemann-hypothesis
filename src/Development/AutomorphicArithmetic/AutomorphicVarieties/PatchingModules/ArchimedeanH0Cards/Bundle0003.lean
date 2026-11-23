module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DegSplit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem deg_split (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 (Lp L))) (w : HeightOneSpectrum (𝓞 L))
    (hA : IsPlaceOver A v) (hw : IsPlaceOver A w) (hv : ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal)
    (hsp : Dec (F := Lp L) A ≤ (resP L Ω).range) : locDeg w = locDeg v := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hlw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
    have h1 := (hA ((l : ℕ) : 𝓞 (Lp L))).mpr hv
    apply (hw ((l : ℕ) : 𝓞 L)).mp
    simpa using h1
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hw hlw
  subst hj
  obtain ⟨-, φL, -, hφL, hrL, -, -, hiL⟩ := (UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, φP, -, hφP, hrP, -, -, hiP⟩ := (UpperTheory.V.Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j
  rw [← hiL w hw, ← hiP v hA]
  congr 1
  ext σ
  constructor
  · intro hσ
    apply (hrP σ).mpr
    intro x
    rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
    exact (hrL σ).mp hσ _
  · intro hσ
    apply (hrL σ).mpr
    intro x
    obtain ⟨g, rfl⟩ := hσ
    obtain ⟨k, hk⟩ := hsp g.2
    rw [hφP]
    congr 1
    rw [← hk]
    exact k.commutes x

theorem UpperTheory.V.Pa.B2.arSum :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∑ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = Module.finrank ℚ (Lp L) := by
  intro l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r
  have key : ∀ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = locDeg (Subtype.val v) := fun v =>
    deg_split l L Ω (s.A v.1) v.1 (s.w v.1) (s.hA _) (s.hw _) v.2 (s.split _ (Or.inl v.2))
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  letI : Fintype {v : HeightOneSpectrum (𝓞 (Lp L)) // ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal} := (locOf r).finV
  have h := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg (Lp L) l
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H2RightExactModLOfH3Subsingleton
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

end

private theorem dn_two_apply' {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 2 → G) → M) (g : Fin 3 → G) :
    dn rho 2 F g = rho (g 0) (F ![g 1, g 2]) - F ![g 0 * g 1, g 2] + F ![g 0, g 1 * g 2] - F ![g 0, g 1] := by
  have e0 : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3]
  abel

private theorem dn_three_apply {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 3 → G) → M) (g : Fin 4 → G) :
    dn rho 3 F g = rho (g 0) (F ![g 1, g 2, g 3]) - F ![g 0 * g 1, g 2, g 3] + F ![g 0, g 1 * g 2, g 3]
      - F ![g 0, g 1, g 2 * g 3] + F ![g 0, g 1, g 2] := by
  have e0 : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1, g 2 * g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e4 : Fin.contractNth 3 (fun x y : G => x * y) g = ![g 0, g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3, e4]
  abel

theorem UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton :
    ∀ (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) → Subsingleton (Hn M.ρ 3)) → SecondCohomologyRightExactModL l G := by
  intro l G _ _ _ h A _ M M' hl u hu hs
  intro x
  obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ x
  set s := Function.surjInv hs with hs_def
  have us : ∀ y, u (s y) = y := Function.surjInv_eq hs
  let c : G × G → M.X := fun p => s (c'.1 p)
  have hc : Continuous c := (continuous_of_discreteTopology (f := s)).comp c'.2.1
  let N : Submodule A M.X := LinearMap.ker u
  have hN : ∀ g : G, ∀ m ∈ N, M.ρ g m ∈ N := by
    intro g m hm
    simp only [N, LinearMap.mem_ker] at hm ⊢
    rw [hu, hm, map_zero]
  let ρK : Representation A G N :=
    { toFun := fun g => (M.ρ g).restrict (hN g)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro g g'
        ext m
        simp }
  have hcont : ContAction ρK :=
    continuous_induced_rng.2 (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let K : FRep A G := FRep.mk N ρK hcont
  have hKl : ∀ m : K.X, l • m = 0 := by
    intro m
    exact Subtype.ext (hl m.1)
  have hsub := h A K hKl
  let C : (Fin 2 → G) → M.X := fun x => c (x 0, x 1)
  have hfN : ∀ g : Fin 3 → G, dn M.ρ 2 C g ∈ N := by
    intro g
    simp only [N, LinearMap.mem_ker]
    rw [dn_two_apply']
    simp only [C, c, map_sub, map_add (f := _), hu, us]
    simpa using c'.2.2 (g 0) (g 1) (g 2)
  let f : (Fin 3 → G) → N := fun g => ⟨dn M.ρ 2 C g, hfN g⟩
  have key : ∀ t : Fin 3 → G, ((f t : N) : M.X) =
      M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := by
    intro t
    simp [f, dn_two_apply', C]
  have hρK : ∀ (a : G) (m : N), ((ρK a m : N) : M.X) = M.ρ a m := fun a m => rfl
  have hmul : ∀ (a b : G) (m : M.X), M.ρ a (M.ρ b m) = M.ρ (a * b) m := by
    intro a b m
    simp [map_mul]
  have fcont : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f) = fun t : Fin 3 → G =>
        M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := funext key
    rw [e]
    have c0 := continuous_apply (A := fun _ : Fin 3 => G) 0
    have c1 := continuous_apply (A := fun _ : Fin 3 => G) 1
    have c2 := continuous_apply (A := fun _ : Fin 3 => G) 2
    exact (((M.cont.comp (c0.prodMk (hc.comp (c1.prodMk c2)))).sub
      (hc.comp ((c0.mul c1).prodMk c2))).add (hc.comp (c0.prodMk (c1.mul c2)))).sub
      (hc.comp (c0.prodMk c1))
  have fcyc : dn ρK 3 f = 0 := by
    funext g
    apply Subtype.ext
    rw [dn_three_apply]
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Pi.zero_apply, ZeroMemClass.coe_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_sub, map_add, hmul]
    simp only [mul_assoc]
    abel
  have fmem : f ∈ Zn K.ρ 3 := by
    refine Submodule.mem_inf.2 ⟨fcont, ?_⟩
    exact LinearMap.mem_ker.2 fcyc
  have h0 : (Submodule.Quotient.mk ⟨f, fmem⟩ : Hn K.ρ 3) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
  change f ∈ Submodule.map (dn ρK 2) (Cn ρK 2) at h0
  obtain ⟨b, hb, hbf⟩ := h0
  have hbc : Continuous b := hb
  have hv : Continuous fun p : G × G => ![p.1, p.2] := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  let c2 : G × G → M.X := fun p => c p - (b ![p.1, p.2] : M.X)
  have hc2 : c2 ∈ Z2 M.ρ := by
    refine ⟨hc.sub (continuous_subtype_val.comp (hbc.comp hv)), ?_⟩
    intro g g' g''
    have e := congrArg Subtype.val (congrFun hbf ![g, g', g''])
    rw [dn_two_apply'] at e
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e
    simp only [c2, map_sub]
    calc _ = (M.ρ g (c (g', g'')) - c (g * g', g'') + c (g, g' * g'') - c (g, g'))
          - (M.ρ g (b ![g', g''] : M.X) - (b ![g * g', g''] : M.X) + (b ![g, g' * g''] : M.X)
            - (b ![g, g'] : M.X)) := by abel
      _ = 0 := by rw [e, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨c2, hc2⟩, ?_⟩
  simp only [mapH2, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext p
  show u (c2 p) = c'.1 p
  simp only [c2, c, map_sub, us, LinearMap.mem_ker.1 (b _).2, sub_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.MapConj
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem map_conj {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] {n : ℕ}
    (u : X →ₗ[A] X') (P Q : Matrix (Fin n) (Fin n) A) (M : Matrix (Fin n) (Fin n) X) :
    (P.map (algebraMap A X) * M * Q.map (algebraMap A X)).map u =
      P.map (algebraMap A X') * M.map u * Q.map (algebraMap A X') := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  rw [mul_comm _ (algebraMap A X _), mul_comm _ (algebraMap A X' _), ← Algebra.smul_def, ← Algebra.smul_def,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]

private def odMap {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (n a : ℕ)
    (u : X →ₗ[A] X') : Od A X n a →ₗ[A] Od A X' n a where
  toFun M := ⟨(M : Matrix (Fin n) (Fin n) X).map u, fun i j => ⟨fun e => by
    have := (M.2 i j).1 e
    rw [Submodule.mem_bot] at this ⊢
    rw [Matrix.map_apply, this, map_zero], fun _ => Submodule.mem_top⟩⟩
  map_add' M N := by ext i j; simp
  map_smul' c M := by ext i j; simp

private theorem lift_ex {A M Q Q' : Type} [CommRing A] [AddCommGroup M] [AddCommGroup Q]
    [AddCommGroup Q'] [Module A M] [Module A Q] [Module A Q'] (π : M →ₗ[A] Q)
    (hπ : Function.Surjective π) (g : M →ₗ[A] Q') (hk : ∀ m, π m = 0 → g m = 0) :
    ∃ q : Q →ₗ[A] Q', ∀ m, q (π m) = g m :=
  _root_.UpperTheory.Reformulated.B.Qf12.lift_ex π hπ g hk

theorem UpperTheory.V.Pa.B2.odHom :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X' : Type) [CommRing X'] [Algebra x.A X'] (D D' : Dat x.A (plOf G)) (o : IsOd h x X D) (o' : IsOd h x X' D') (u : X →ₗ[x.A] X'), ∃ f : D.Hom D', Induced o o' u f := by
  intro l _ L G G0 h n x X _ _ X' _ _ D D' o o' u
  let f : D.M.X →ₗ[x.A] D'.M.X := o'.e.symm.toLinearMap ∘ₗ odMap n x.a u ∘ₗ o.e.toLinearMap
  have hf : ∀ m, (o'.e (f m) : Matrix (Fin n) (Fin n) X') = (o.e m : Matrix (Fin n) (Fin n) X).map u := fun m => by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have h0 : ∀ (g : G.G₀) m, f (D.M.ρ g m) = D'.M.ρ g (f m) := fun g m => by
    apply o'.e.injective
    apply Subtype.ext
    rw [hf, o.act, o'.act, hf]
    exact map_conj u _ _ _
  have hc : ∀ m, f (D.M.ρ G.c m) = D'.M.ρ G.c (f m) := fun m => by
    apply o'.e.injective
    apply Subtype.ext
    rw [hf, o.actc, o'.actc, hf]
    ext i j
    simp
  have hall : ∀ (g : G.Γ) m, f (D.M.ρ g m) = D'.M.ρ g (f m) := fun g m => by
    rcases Int.units_eq_one_or (G.η g) with e | e
    · exact h0 ⟨g, e⟩ m
    · have hm : g * G.c ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, e, G.η_c]; simp
      have eg : g * G.c * G.c = g := by rw [mul_assoc, G.c_sq, mul_one]
      have e1 := h0 ⟨g * G.c, hm⟩ (D.M.ρ G.c m)
      rw [hc, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul] at e1
      simpa only [eg] using e1
  have hk : ∀ w m, D.π w m = 0 → (D'.π w ∘ₗ f) m = 0 := by
    rintro (v | w) m hm
    · rw [LinearMap.comp_apply, o'.kerV]
      intro i j hij
      have e := congrFun (congrFun (map_conj u (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A)
        (x.w v : Matrix (Fin n) (Fin n) x.A) (o.e m : Matrix (Fin n) (Fin n) X)) i) j
      rw [hf]
      refine e.symm.trans ?_
      have := (o.kerV v m).1 hm i j hij
      rw [Matrix.map_apply]
      exact (congrArg u this).trans (map_zero u)
    · have : m = 0 := o.kerU w (hm.trans (map_zero _).symm)
      rw [this, map_zero]
  choose q hq using fun w => lift_ex (D.π w) (D.surj w) (D'.π w ∘ₗ f) (hk w)
  exact ⟨⟨f, q, hall, hq⟩, hf⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdSESInv
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem map_algebraMap_mul_mul_map_linearMap {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (P Q : Matrix (Fin n) (Fin n) x.A) (N : Matrix (Fin n) (Fin n) Y) :
    (P.map (algebraMap x.A Y) * N * Q.map (algebraMap x.A Y)).map u = P.map (algebraMap x.A Z) * N.map u * Q.map (algebraMap x.A Z) := by
  have key : ∀ (p q : x.A) (y : Y), u (algebraMap x.A Y p * y * algebraMap x.A Y q) = algebraMap x.A Z p * u y * algebraMap x.A Z q := by
    intro p q y
    have h1 : algebraMap x.A Y p * y * algebraMap x.A Y q = (p * q) • y := by
      rw [Algebra.smul_def, map_mul]; ring
    have h2 : algebraMap x.A Z p * u y * algebraMap x.A Z q = (p * q) • u y := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [h1, h2, map_smul]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => key _ _ _

private theorem exists_matrix_map_eq_of_zero_on_of_mem_range {n : ℕ} {R Y Z : Type} [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (w : Y →ₗ[R] Z) (S : Fin n → Fin n → Prop) (N : Matrix (Fin n) (Fin n) Z) (h0 : ∀ i j, S i j → N i j = 0) (hr : ∀ i j, ¬ S i j → N i j ∈ Set.range w) :
    ∃ N' : Matrix (Fin n) (Fin n) Y, (∀ i j, S i j → N' i j = 0) ∧ N'.map w = N := by
  classical
  refine ⟨Matrix.of fun i j => if h : S i j then 0 else (hr i j h).choose, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · ext i j
    by_cases hij : S i j
    · simp [hij, h0 i j hij]
    · simp [hij, (hr i j hij).choose_spec]

private theorem mem_od_iff_entry_eq_zero_of_same_block {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} (N : Matrix (Fin n) (Fin n) R) :
    N ∈ Od A R n a ↔ ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → N i j = 0 := by
  constructor
  · intro hN i j hij
    exact (Submodule.mem_bot _).1 ((hN i j).1 hij)
  · intro hN i j
    exact ⟨fun hij => (Submodule.mem_bot _).2 (hN i j hij), fun _ => Submodule.mem_top⟩

private theorem inv_w_entry_eq_zero_of_ty_ne_lt_a {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (j k : Fin n) (hjk : x.ty v j ≠ decide ((k : ℕ) < x.a)) :
    (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) j k = 0 := by
  classical
  set W : Matrix (Fin n) (Fin n) (PowerSeries x.K) := ((x.w v : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hW
  set B : Matrix (Fin n) (Fin n) (PowerSeries x.K) := (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hB
  have hBW : B * W = 1 := Units.inv_mul (x.w v)
  have hWB : W * B = 1 := Units.mul_inv (x.w v)
  let β : Bool → PowerSeries x.K := fun b => if b then 1 else 0
  have hpat : W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) = Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * W := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : decide ((i : ℕ) < x.a) = x.ty v j
    · rw [h]; ring_nf
    · rw [show W i j = 0 from x.w_blk v i j h]; simp
  have key : Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) := by
    calc Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B := by
          rw [hBW, Matrix.one_mul]
      _ = B * (W * Matrix.diagonal (fun j : Fin n => β (x.ty v j))) * B := by rw [Matrix.mul_assoc B]
      _ = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * (W * B) := by
          rw [hpat]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWB, Matrix.mul_one]
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (PowerSeries x.K) => M j k) key
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
  change B j k = 0
  cases h1 : x.ty v j <;> cases h2 : decide ((k : ℕ) < x.a) <;> simp only [h1, h2, β] at e hjk <;> simp_all

private theorem wiX_mul_mul_wX_eq_zero_of_ty_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (N : Matrix (Fin n) (Fin n) Y) (hN : ∀ k l : Fin n, ((k : ℕ) < x.a ↔ (l : ℕ) < x.a) → N k l = 0) (i j : Fin n) (hij : x.ty v i = x.ty v j) :
    (x.wiX Y v * N * x.wX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : x.ty v i = decide ((k : ℕ) < x.a)
  · by_cases h2 : decide ((l : ℕ) < x.a) = x.ty v j
    · rw [hN k l (decide_eq_decide.mp (by rw [← h1, hij, ← h2]))]; simp
    · simp [NP.wX, x.w_blk v l j h2]
  · simp only [NP.wiX, Matrix.map_apply]
    rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v i k h1]; simp

private theorem wX_mul_mul_wiX_eq_zero_of_same_block {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (P : Matrix (Fin n) (Fin n) Y) (hP : ∀ k l : Fin n, x.ty v k = x.ty v l → P k l = 0) (i j : Fin n) (hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) :
    (x.wX Y v * P * x.wiX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : decide ((i : ℕ) < x.a) = x.ty v k
  · by_cases h2 : x.ty v l = decide ((j : ℕ) < x.a)
    · rw [hP k l (by rw [← h1, h2]; exact decide_eq_decide.mpr hij)]; simp
    · simp only [NP.wiX, Matrix.map_apply]
      rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v l j h2]; simp
  · simp [NP.wX, x.w_blk v i k h1]

private theorem map_wiX_mul_mul_wX_and_wX_mul_mul_wiX {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (N : Matrix (Fin n) (Fin n) Y) :
    (x.wiX Y v * N * x.wX Y v).map u = x.wiX Z v * N.map u * x.wX Z v ∧
      (x.wX Y v * N * x.wiX Y v).map u = x.wX Z v * N.map u * x.wiX Z v := by
  unfold NP.wX NP.wiX
  exact ⟨map_algebraMap_mul_mul_map_linearMap x u _ _ N, map_algebraMap_mul_mul_map_linearMap x u _ _ N⟩

private theorem wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] :
    x.wiX Y v * x.wX Y v = 1 ∧ x.wX Y v * x.wiX Y v = 1 := by
  unfold NP.wX NP.wiX
  constructor
  · rw [← Matrix.map_mul, Units.inv_mul]; simp
  · rw [← Matrix.map_mul, Units.mul_inv]; simp

theorem UpperTheory.V.Pa.B2.odSES :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X' : Type) [CommRing X'] [Algebra x.A X'] (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D' D D'' : Dat x.A (plOf G)) (o' : IsOd h x X' D') (o : IsOd h x X D) (o'' : IsOd h x X'' D'') (u : X' →ₗ[x.A] X) (v : X →ₗ[x.A] X'') (f : D'.Hom D) (g : D.Hom D''), Induced o' o u f → Induced o o'' v g → Function.Injective u → Function.Exact u v → Function.Surjective v → Dat.SES f g := by
  intro l _ L G G0 h n x X' _ _ X _ _ X'' _ _ D' D D'' o' o o'' u v f g hf hg hu hex hv
  have inj : Function.Injective f.f := by
    intro m1 m2 h12
    apply o'.e.injective
    apply Subtype.ext
    have e1 := hf m1
    rw [h12, hf m2] at e1
    ext i j
    exact hu (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X => M i j) e1.symm)
  have ex : Function.Exact f.f g.f := by
    intro m
    constructor
    · intro hgm
      have h0 : (↑(o.e m) : Matrix (Fin n) (Fin n) X).map v = 0 := by
        rw [← hg m, hgm]; simp
      obtain ⟨N', hN'0, hN'⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range u (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o.e m))
        (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o.e m).2 i j hij)
        (fun i j _ => (hex _).1 (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X'' => M i j) h0))
      refine ⟨o'.e.symm ⟨N', (mem_od_iff_entry_eq_zero_of_same_block _).2 hN'0⟩, ?_⟩
      apply o.e.injective
      apply Subtype.ext
      rw [hf, LinearEquiv.apply_symm_apply]
      exact hN'
    · rintro ⟨m', rfl⟩
      apply o''.e.injective
      apply Subtype.ext
      rw [hg, hf, map_zero]
      ext i j
      simpa using (hex _).2 ⟨_, rfl⟩
  have surj : Function.Surjective g.f := by
    intro m''
    obtain ⟨N, hN0, hN⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o''.e m''))
      (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e m'').2 i j hij) (fun i j _ => hv _)
    refine ⟨o.e.symm ⟨N, (mem_od_iff_entry_eq_zero_of_same_block _).2 hN0⟩, ?_⟩
    apply o''.e.injective
    apply Subtype.ext
    rw [hg, LinearEquiv.apply_symm_apply]
    exact hN
  refine ⟨inj, ex, surj, ?_, ?_⟩
  · intro w
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := D'.surj w q
    rw [f.comm] at hq
    rcases w with w | w
    · rw [o'.kerV]
      rw [o.kerV] at hq
      intro i j hji
      have e := hq i j hji
      rw [hf, ← (map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w u _).1, Matrix.map_apply] at e
      exact hu (by rw [map_zero]; exact e)
    · have h1 : f.f m = 0 := o.kerU w (by rw [hq, map_zero])
      rw [inj (h1.trans (map_zero f.f).symm), map_zero]
  · intro w q
    constructor
    · intro hq
      obtain ⟨m, rfl⟩ := D.surj w q
      rw [g.comm] at hq
      rcases w with w | w
      · have hlow := (o''.kerV w (g.f m)).1 hq
        obtain ⟨P, hP0, hP⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => j < i ∨ x.ty w i = x.ty w j)
          (x.wiX X'' w * (↑(o''.e (g.f m)) : Matrix (Fin n) (Fin n) X'') * x.wX X'' w)
          (fun i j hij => hij.elim (hlow i j) (wiX_mul_mul_wX_eq_zero_of_ty_eq x w _ ((mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e (g.f m)).2) i j))
          (fun i j _ => hv _)
        have hN : x.wX X w * P * x.wiX X w ∈ Od x.A X n x.a :=
          (mem_od_iff_entry_eq_zero_of_same_block _).2 (fun i j hij => wX_mul_mul_wiX_eq_zero_of_same_block x w P (fun k l hkl => hP0 k l (Or.inr hkl)) i j hij)
        obtain ⟨h1, h2⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X)
        obtain ⟨h1'', h2''⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X'')
        have hconj : x.wiX X w * (↑(o.e (o.e.symm ⟨_, hN⟩)) : Matrix (Fin n) (Fin n) X) * x.wX X w = P := by
          rw [LinearEquiv.apply_symm_apply]
          show x.wiX X w * (x.wX X w * P * x.wiX X w) * x.wX X w = P
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hk : D.π (Sum.inl w) (o.e.symm ⟨_, hN⟩) = 0 :=
          (o.kerV w _).2 (fun i j hji => by rw [hconj]; exact hP0 i j (Or.inl hji))
        have hg0 : g.f (o.e.symm ⟨_, hN⟩) = g.f m := by
          apply o''.e.injective
          apply Subtype.ext
          rw [hg (o.e.symm ⟨_, hN⟩), LinearEquiv.apply_symm_apply]
          show (x.wX X w * P * x.wiX X w).map v = _
          rw [(map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w v P).2, hP]
          simp only [Matrix.mul_assoc, h2'', Matrix.mul_one]
          rw [← Matrix.mul_assoc, h2'', Matrix.one_mul]
        have hdiff : g.f (m - o.e.symm ⟨_, hN⟩) = 0 := by rw [map_sub, hg0, sub_self]
        obtain ⟨m', hm'⟩ := (ex _).1 hdiff
        refine ⟨D'.π _ m', (f.comm _ m').trans ?_⟩
        rw [hm', map_sub, hk, sub_zero]
      · have h1 : g.f m = 0 := o''.kerU w (by rw [hq, map_zero])
        obtain ⟨m', hm'⟩ := (ex m).1 h1
        exact ⟨D'.π _ m', (f.comm _ m').trans (congrArg _ hm')⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨m', rfl⟩ := D'.surj w q'
      rw [f.comm, g.comm, (ex (f.f m')).2 ⟨m', rfl⟩, map_zero]
end

