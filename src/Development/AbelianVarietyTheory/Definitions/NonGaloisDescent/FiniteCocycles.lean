module

public import Mathlib

@[expose] public section

noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

def AdicCont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) : Prop :=
  ∀ N : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (I ^ N) (f g)

structure Det (n : ℕ) (A E : Type) [CommRing A] [Ring E] [Algebra A E] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], B ⊗[A] E →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : B ⊗[A] E),
    D B' (Algebra.TensorProduct.map f (AlgHom.id A E) x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : B ⊗[A] E), D B (b • x) = b ^ n * D B x

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

def chi (y : E) : A[X] := D.D A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)

def lam (i : ℕ) (y : E) : A := (-1) ^ i * (D.chi y).coeff (n - i)

def tr (y : E) : A := D.lam 1 y

end Det

structure GDet (n : ℕ) (A G : Type) [CommRing A] [Group G] : Type 1 where
  D : ∀ (B : Type) [CommRing B] [Algebra A B], MonoidAlgebra B G →* B
  nat : ∀ (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (f : B →ₐ[A] B') (x : MonoidAlgebra B G),
    D B' (MonoidAlgebra.mapRingHom G (f : B →+* B') x) = f (D B x)
  homog : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B) (x : MonoidAlgebra B G), D B (b • x) = b ^ n * D B x

namespace GDet

variable {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)

def map {A' : Type} [CommRing A'] (f : A →+* A') : GDet n A' G where
  D B _ _ := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.D B
  nat B B' _ _ _ _ g x :=
    letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    letI : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
    D.nat B B' { (g : B →+* B') with commutes' := fun a => g.commutes (f a) } x
  homog B _ _ b x := letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra; D.homog B b x

def repAlg {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι A) (B : Type) [CommRing B] [Algebra A B] :
    MonoidAlgebra B G →ₐ[B] Matrix ι ι B :=
  MonoidAlgebra.lift B (Matrix ι ι B) G ((RingHom.mapMatrix (algebraMap A B)).toMonoidHom.comp ρ)

def ofRep (ρ : G →* Matrix (Fin n) (Fin n) A) : GDet n A G where
  D B _ _ := Matrix.detMonoidHom.comp (repAlg ρ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (repAlg ρ B' _).det = f (repAlg ρ B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => ext i j; simp [repAlg]
  homog B _ _ b x := by
    change (repAlg ρ B (b • x)).det = b ^ n * (repAlg ρ B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]

def chi (y : MonoidAlgebra A G) : A[X] := D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)

def lam (i : ℕ) (y : MonoidAlgebra A G) : A := (-1) ^ i * (D.chi y).coeff (n - i)

def tr (y : MonoidAlgebra A G) : A := D.lam 1 y

def gen {m : ℕ} (y : Fin m → MonoidAlgebra A G) : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
  ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) A) • MonoidAlgebra.mapRingHom G MvPolynomial.C (y j)

def CH : Set (MonoidAlgebra A G) :=
  {z | ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ), ∀ g : G,
    z.coeff g = AddMonoidAlgebra.coeff ((Polynomial.aeval (gen y) ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (gen y))).coeff g)
      β}

variable [TopologicalSpace G]

def IsCont (I : Ideal A) : Prop := ∀ i, AdicCont I fun g : G => D.lam i (MonoidAlgebra.single g 1)

end GDet

end GlobalTheory.Pat

noncomputable section

open IsLocalRing

namespace GlobalTheory.Pat

def ContM {X : Type} [TopologicalSpace X] (A : Type) [CommRing A] [IsLocalRing A] (f : X → A) : Prop :=
  AdicCont (maximalIdeal A) f

def PhiFin (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, IsOpen (H : Set G) →
    {f : H →* Multiplicative (ZMod l) | IsOpen (f.ker : Set H)}.Finite

theorem PhiFin.of_finite (l : ℕ) [NeZero l] (G : Type) [Group G] [Finite G] [TopologicalSpace G] : PhiFin l G := by
  intro H _
  haveI : Finite (H →* Multiplicative (ZMod l)) := Finite.of_injective _ DFunLike.coe_injective
  exact Set.toFinite _

def TopGen (B : Type) [CommRing B] [IsLocalRing B] (S : Set B) : Prop :=
  ∀ (N : ℕ) (a : B), ∃ b ∈ Subring.closure S, a - b ∈ maximalIdeal B ^ N

structure PG where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  [tgrp : IsTopologicalGroup G]
  [cpt : CompactSpace G]
  [t2 : T2Space G]
  [td : TotallyDisconnectedSpace G]

instance : CoeSort PG Type := ⟨PG.G⟩

attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td

structure Frame where
  n : ℕ
  n_pos : 0 < n
  l : ℕ
  [hl : Fact l.Prime]
  l_odd : l ≠ 2
  O : Type
  [iO : CommRing O] [iOd : IsDomain O] [iOv : IsDiscreteValuationRing O]
  O_cpl : IsAdicComplete (maximalIdeal O) O
  k_fin : Finite (ResidueField O)
  l_mem : (l : O) ∈ maximalIdeal O
  d0 : ℕ
  Vl : Type
  [iVl : Fintype Vl]
  Gv : Vl → PG
  Gv_phi : ∀ v, PhiFin l (Gv v).G
  Mu : ∀ v, Subgroup (Gv v).G
  psib : ∀ v, Fin n → (Gv v).G →* (ResidueField O)ˣ
  St : Type
  [iSt : Fintype St]
  Iu : St → PG
  Iu_phi : ∀ u, PhiFin l (Iu u).G

  Lk : ∀ v, Set (Fin n × (Gv v).G × MvPowerSeries (Fin d0) O)
  Lk_gen : TopGen (MvPowerSeries (Fin d0) O)
    (Set.range (MvPowerSeries.C : O →+* MvPowerSeries (Fin d0) O) ∪ {a | ∃ v i g, (i, g, a) ∈ Lk v})
  Lk_mu : ∀ v i, ∀ g ∈ Mu v, ∃ θ : O, θ - 1 ∈ maximalIdeal O ∧ (i, g, MvPowerSeries.C θ) ∈ Lk v

attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt

namespace Frame
variable (Φ : Frame)

abbrev k : Type := ResidueField Φ.O

abbrev abelian₂ : Type := MvPowerSeries (Fin Φ.d0) Φ.O

abbrev A : Type := PowerSeries Φ.k

end Frame

structure PolGp (Φ : Frame) where
  Γ : PG
  sig : Γ.G →* Γ.G
  sig_cont : Continuous sig
  sig_sig : ∀ g, sig (sig g) = g
  mu : Γ.G →* Φ.Oˣ
  mu_cont : ContM Φ.O (fun g => ((mu g : Φ.Oˣ) : Φ.O))
  mu_sig : ∀ g, mu (sig g) = mu g
  iv : ∀ v, (Φ.Gv v).G →* Γ.G
  iv_cont : ∀ v, Continuous (iv v)
  iu : ∀ u, (Φ.Iu u).G →* Γ.G
  iu_cont : ∀ u, Continuous (iu u)
  chi : Fin Φ.n → (Γ.G →* Φ.kˣ)
  chi_open : ∀ i, IsOpen ((chi i).ker : Set Γ.G)
  chi_inj : Function.Injective chi

  fg : PhiFin Φ.l Γ.G

abbrev DetG (n : ℕ) (Γ B : Type) [Group Γ] [CommRing B] : Type 1 := GDet n B Γ

abbrev gp {Γ : Type} (B : Type) [Group Γ] [CommRing B] (g : Γ) : MonoidAlgebra B Γ := MonoidAlgebra.single g 1

abbrev sc {B : Type} (Γ : Type) [Group Γ] [CommRing B] (b : B) : MonoidAlgebra B Γ := MonoidAlgebra.single 1 b

def DetCont {n : ℕ} {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing B] [IsLocalRing B]
    (D : DetG n Γ B) : Prop :=
  D.IsCont (maximalIdeal B)

def Red {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] (j : O →+* B) (b : B)
    (x : ResidueField O) : Prop :=
  ∃ o : O, residue O o = x ∧ b - j o ∈ maximalIdeal B

def diagRep {n : ℕ} {Γ K : Type} [Group Γ] [CommRing K] (chi : Fin n → (Γ →* Kˣ)) :
    Γ →* Matrix (Fin n) (Fin n) K where
  toFun g := Matrix.diagonal (fun i => ((chi i g : Kˣ) : K))
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]

def DetLifts {n : ℕ} {Γ O B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B]
    (j : O →+* B) (D : DetG n Γ B) (chi : Fin n → (Γ →* (ResidueField O)ˣ)) : Prop :=
  ∀ κ : ResidueField O →+* ResidueField B, κ.comp (residue O) = (residue B).comp j →
    D.map (residue B) = (GDet.ofRep (diagRep chi)).map κ

structure IsCNL {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] (j : O →+* B) :
    Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  loc : IsLocalHom j
  res : Function.Surjective ((residue B).comp j)

section Elements
variable {Φ : Frame} (G : PolGp Φ) {B : Type} [CommRing B]

def star (j : Φ.O →+* B) (x : MonoidAlgebra B G.Γ.G) : MonoidAlgebra B G.Γ.G :=
  x.coeff.sum (fun g a => MonoidAlgebra.single (G.sig g)⁻¹ (a * j ((G.mu g : Φ.Oˣ) : Φ.O)))

def oEl (v : Φ.Vl) (ψ : Fin Φ.n → ((Φ.Gv v).G →* Bˣ)) (g : Fin Φ.n → (Φ.Gv v).G) : MonoidAlgebra B G.Γ.G :=
  (List.ofFn fun i => gp B (G.iv v (g i)) - sc G.Γ.G ((ψ i (g i) : Bˣ) : B)).prod

end Elements

structure Pair {Φ : Frame} (G : PolGp Φ) where
  B : Type
  [iB : CommRing B] [iL : IsLocalRing B]
  lam : Φ.abelian₂ →+* B
  lam_loc : IsLocalHom lam
  cnl : IsCNL (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂))
  D : DetG Φ.n G.Γ.G B
  psi : ∀ v, Fin Φ.n → ((Φ.Gv v).G →* Bˣ)
  cont : DetCont D
  lift : DetLifts (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) D G.chi
  psi_cont : ∀ v i, ContM B (fun g => ((psi v i g : Bˣ) : B))
  psi_lift : ∀ v i g, Red (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) ((psi v i g : Bˣ) : B)
    ((Φ.psib v i g : Φ.kˣ) : Φ.k)
  link : ∀ v i g a, (i, g, a) ∈ Φ.Lk v → ((psi v i g : Bˣ) : B) = lam a
  relP : ∀ (g : G.Γ.G) (i : ℕ),
    D.lam i (star G (lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)) (gp B g)) = D.lam i (gp B g)
  relO : ∀ v (g : Fin Φ.n → (Φ.Gv v).G) (h : G.Γ.G), D.tr (gp B h * oEl G v (psi v) g) = 0
  relI : ∀ u (g : (Φ.Iu u).G) (h : G.Γ.G), D.tr (gp B h * (gp B (G.iu u g) - 1)) = 0

attribute [instance] Pair.iB Pair.iL

namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)

def j : Φ.O →+* R.B := R.lam.comp (MvPowerSeries.C : Φ.O →+* Φ.abelian₂)

end Pair

section CH
variable {n : ℕ} {Γ B : Type} [Group Γ] [CommRing B] (D : DetG n Γ B)

end CH

namespace Pair
variable {Φ : Frame} {G : PolGp Φ} (R : Pair G)

end Pair

end GlobalTheory.Pat

noncomputable section

open IsLocalRing Polynomial

namespace GlobalTheory.Pat.Example

theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A G) :
    (GDet.ofRep ρ).chi y = (GDet.repAlg ρ A y).charpoly := by
  change (GDet.repAlg ρ A[X] _).det = _
  unfold Matrix.charpoly Matrix.charmatrix
  congr 1
  rw [map_sub]
  congr 1
  · ext i j; simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => ext i j; simp [GDet.repAlg]

theorem tr_ofRep {n : ℕ} {A G : Type} [CommRing A] [Nontrivial A] [Group G]
    (ρ : G →* Matrix (Fin (n+1)) (Fin (n+1)) A) (y : MonoidAlgebra A G) :
    (GDet.ofRep ρ).tr y = (GDet.repAlg ρ A y).trace := by
  unfold GDet.tr GDet.lam
  rw [chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff]
  simp

def finPG (G : Type) [Group G] [Finite G] : PG :=
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  { G := G }

instance (G : Type) [Group G] [Finite G] : DiscreteTopology (finPG G) := ⟨rfl⟩

instance (G : Type) [Group G] [Finite G] : Finite (finPG G) := inferInstanceAs (Finite G)

theorem adic {X R : Type} [TopologicalSpace X] [DiscreteTopology X] [CommRing R] (I : Ideal R) (f : X → R) :
    AdicCont I f := fun _ => IsLocallyConstant.of_discrete _

abbrev S3 := DihedralGroup 3

def rZ : S3 → Matrix (Fin 2) (Fin 2) ℤ
  | .r i => if i = 0 then !![1,0;0,1] else if i = 1 then !![1,1;-3,-2] else !![-2,-1;3,1]
  | .sr i => if i = 0 then !![1,1;0,-1] else if i = 1 then !![-2,-1;3,2] else !![1,0;-3,-1]

def rhoZ : S3 →* Matrix (Fin 2) (Fin 2) ℤ where
  toFun := rZ
  map_one' := by decide
  map_mul' := by decide

def sgn : S3 →* ℤˣ where
  toFun g := match g with | .r _ => 1 | .sr _ => -1
  map_one' := by decide
  map_mul' := by decide

def inc : ℤˣ →* S3 where
  toFun u := if u = 1 then 1 else .sr 0
  map_one' := by decide
  map_mul' := by decide

def rho (A : Type) [CommRing A] : S3 →* Matrix (Fin 2) (Fin 2) A :=
  (Int.castRingHom A).mapMatrix.toMonoidHom.comp rhoZ

def chs (A : Type) [CommRing A] : Fin 2 → (ℤˣ →* Aˣ) := ![1, Units.map (Int.castRingHom A).toMonoidHom]

theorem three_mem : ((3 : ℕ) : ℤ_[3]) ∈ maximalIdeal ℤ_[3] := by
  rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _

def frame : Frame where
  n := 2
  n_pos := by norm_num
  l := 3
  l_odd := by norm_num
  O := ℤ_[3]
  O_cpl := inferInstance
  k_fin := Finite.of_equiv _ (PadicInt.residueField (p := 3)).symm.toEquiv
  l_mem := three_mem
  d0 := 0
  Vl := Unit
  Gv _ := finPG ℤˣ
  Gv_phi _ := PhiFin.of_finite 3 _
  Mu _ := ⊥
  psib _ := chs _
  St := Unit
  Iu _ := finPG ℤˣ
  Iu_phi _ := PhiFin.of_finite 3 _
  Lk _ := {x | x.2.2 = MvPowerSeries.C ((chs ℤ_[3] x.1 x.2.1 : ℤ_[3]ˣ) : ℤ_[3])}
  Lk_gen := by
    intro N a
    refine ⟨a, Subring.subset_closure (Or.inl ⟨MvPowerSeries.constantCoeff a, ?_⟩), by simp⟩
    ext m
    have : m = 0 := Subsingleton.elim _ _
    subst this
    simp
  Lk_mu := by
    intro v i g hg
    refine ⟨1, by simp, ?_⟩
    have : g = 1 := by simpa using hg
    subst this
    change MvPowerSeries.C 1 = MvPowerSeries.C ((chs ℤ_[3] i 1 : ℤ_[3]ˣ) : ℤ_[3])
    simp

theorem three_k : (3 : ResidueField ℤ_[3]) = 0 := by
  have := (residue_eq_zero_iff _).2 three_mem
  rw [map_natCast] at this
  exact_mod_cast this

theorem neg_one_ne : (-1 : ResidueField ℤ_[3]) ≠ 1 := by
  intro h
  have h3 := three_k
  have : (1 : ResidueField ℤ_[3]) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

def pol : PolGp frame where
  Γ := finPG S3
  sig := MonoidHom.id _
  sig_cont := continuous_of_discreteTopology
  sig_sig _ := rfl
  mu := 1
  mu_cont := adic _ _
  mu_sig _ := rfl
  iv _ := inc
  iv_cont _ := continuous_of_discreteTopology (α := finPG ℤˣ)
  iu _ := 1
  iu_cont _ := continuous_of_discreteTopology (α := finPG ℤˣ)
  chi i := (chs _ i).comp sgn
  chi_open _ := isOpen_discrete _
  chi_inj := by
    have key : ((chs (ResidueField ℤ_[3]) 0).comp sgn) ≠ ((chs (ResidueField ℤ_[3]) 1).comp sgn) := by
      intro h
      have := congrArg (fun f => ((f (DihedralGroup.sr 0) : (ResidueField ℤ_[3])ˣ) : ResidueField ℤ_[3])) h
      simp [chs, sgn] at this
      exact neg_one_ne this.symm
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h key
    · exact absurd h.symm key
    · rfl
  fg := PhiFin.of_finite 3 _

theorem rep_gp (A : Type) [CommRing A] (g : S3) : GDet.repAlg (rho A) A (gp A g) = rho A g := by
  simp [GDet.repAlg]

theorem star_gp (j : ℤ_[3] →+* ℤ_[3]) (g : S3) : star pol j (gp ℤ_[3] g) = gp ℤ_[3] g⁻¹ := by
  unfold star
  change (MonoidAlgebra.single g (1 : ℤ_[3])).coeff.sum
    (fun (g : S3) (a : ℤ_[3]) => MonoidAlgebra.single g⁻¹ (a * j 1)) = _
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index] <;> simp

end GlobalTheory.Pat.Example
