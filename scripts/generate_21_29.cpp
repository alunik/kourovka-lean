// Untrusted witness generator. Every emitted assertion is checked by Lean's kernel.
// g = 64*p+d: p<9 is r(p), p>=9 is sr(p-9); d gives six free sign bits.
#include <array>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <vector>

using Vec = std::array<int, 9>;
constexpr int degree = 19683, order = 1152, chunk = 128;
const std::string prefix = "Kourovka.Problems.P21_29.Proof.";

Vec decode(int c) {
  Vec v{};
  for (auto &x : v) { x = c % 3; c /= 3; }
  return v;
}
int encode(const Vec &v) {
  int c = 0;
  for (int x = 8; x >= 0; --x) c = 3*c + v[x];
  return c;
}
Vec act(int g, const Vec &v) {
  const int p = g/64, d = g%64;
  Vec out{};
  for (int x = 0; x < 9; ++x) {
    const int row = x%3, col = x/3;
    const int a = (d>>(2*row))&1, b = (d>>(2*row+1))&1;
    const int bit = col==0 ? a : col==1 ? b : a^b;
    const int y = p<9 ? (x-p+9)%9 : (27-(p-9)-x)%9;
    out[x] = (bit ? 2*v[y] : v[y])%3;
  }
  return out;
}
std::string suffix(int n) {
  std::ostringstream s;
  s << std::setw(3) << std::setfill('0') << n;
  return s.str();
}
std::ofstream output(const std::filesystem::path &dir, const std::string &name) {
  std::ofstream f(dir/(name+".lean"));
  if (!f) throw std::runtime_error("Cannot open output file");
  return f;
}
int main(int argc, char **argv) {
  try {
    if (argc != 2) throw std::runtime_error("Usage: generate_21_29 OUTPUT_DIRECTORY");
    const std::filesystem::path dir(argv[1]);
    std::filesystem::create_directories(dir);
    std::vector<int> fixers(degree, 0);
    for (int c = 0; c < degree; ++c) {
      const auto v = decode(c);
      for (int g = 1; g < order; ++g) {
        if (act(g,v)==v) { fixers[c]=g; break; }
      }
    }
    Vec r{}, hole{};
    r.fill(1); r[0]=0; r[2]=2;
    for (int x=0; x<9; ++x) hole[x] = x%3==0 ? 0 : 1;
    if (fixers[encode(r)])
      throw std::runtime_error("Unexpected regular-vector check");
    std::vector<int> witnesses(degree);
    for (int c=0; c<degree; ++c) {
      if (fixers[c]) { witnesses[c]=fixers[c]; continue; }
      Vec v=decode(c);
      for (int x=0; x<9; ++x) v[x]=(v[x]-hole[x]+3)%3;
      if (!fixers[encode(v)]) throw std::runtime_error("Counterexample check failed");
      witnesses[c]=order+fixers[encode(v)];
    }
    const int chunks=(degree+chunk-1)/chunk;
    for (int j=0; j<chunks; ++j) {
      const int start=j*chunk, length=std::min(chunk,degree-start);
      auto f=output(dir,"Obstruction"+suffix(j));
      f << "import " << prefix << "FiniteModel\n\n"
        << "/-! Generated witnesses; the assertions below are kernel-checked. -/\n\n"
        << "namespace Kourovka.P21_29\n\nprivate def witnesses : Array ℕ := #[";
      for (int k=0; k<length; ++k) f << (k ? ", " : "") << witnesses[start+k];
      f << "]\n\ntheorem obstructionChunk" << suffix(j)
        << " (code : Fin 19683)\n    (_hlo : " << start << " ≤ code.val) (" << (j==chunks-1 ? "_hhi" : "hhi") << " : code.val < "
        << start+length << ") :\n    ∃ w : ℕ, obstructionCheck code.val w = true := by\n"
        << "  have h : ∀ i : Fin " << length << ",\n"
        << "      obstructionCheck (" << start << " + i.val) witnesses[i.val]! = true := by\n"
        << "    decide +kernel\n"
        << "  let i : Fin " << length << " := ⟨code.val - " << start << ", by omega⟩\n"
        << "  refine ⟨witnesses[i.val]!, ?_⟩\n"
        << "  have hi := h i\n"
        << "  have heq : " << start << " + i.val = code.val := by dsimp [i]; omega\n"
        << "  simpa only [heq] using hi\n\nend Kourovka.P21_29\n";
    }
    for (int j=0; j<18; ++j) {
      auto f=output(dir,"Regular"+suffix(j));
      f << "import " << prefix << "FiniteModel\n\nnamespace Kourovka.P21_29\n\n"
        << "private theorem checked : ∀ k : Fin 64,\n"
        << "      groupElement ⟨" << 64*j << " + k.val, by omega⟩ • regularVector = regularVector →\n"
        << "        " << 64*j << " + k.val = 0 := by\n"
        << "    decide +kernel\n"
        << "\ntheorem regularChunk" << suffix(j) << " (i : Fin 1152)\n"
        << "    (_hlo : " << 64*j << " ≤ i.val) (hhi : i.val < " << 64*(j+1) << ") :\n"
        << "    groupElement i • regularVector = regularVector → groupElement i = 1 := by\n"
        << "  let k : Fin 64 := ⟨i.val - " << 64*j << ", by omega⟩\n"
        << "  have heq : (⟨" << 64*j << " + k.val, by omega⟩ : Fin 1152) = i := by\n"
        << "    apply Fin.ext\n    dsimp [k]\n    omega\n"
        << "  intro hg\n"
        << "  have hz := checked k (by simpa only [heq] using hg)\n"
        << "  have hi : i = 0 := by apply Fin.ext; dsimp [k] at hz; omega\n"
        << "  subst i\n"
        << "  apply SemidirectProduct.ext\n  · apply Subtype.ext\n    funext x\n    revert x\n    decide +kernel\n  · rfl\n\nend Kourovka.P21_29\n";
    }
    auto f=output(dir,"Checks");
    for (int j=0;j<chunks;++j) f << "import " << prefix << "Certificates.Obstruction" << suffix(j) << "\n";
    for (int j=0;j<18;++j) f << "import " << prefix << "Certificates.Regular" << suffix(j) << "\n";
    f << "\nnamespace Kourovka.P21_29\n\n"
      << "theorem obstruction_checked (code : Fin 19683) :\n"
      << "    ∃ w : ℕ, obstructionCheck code.val w = true := by\n";
    for (int j=0;j<chunks-1;++j)
      f << "  by_cases h : code.val < " << chunk*(j+1) << "\n"
        << "  · exact obstructionChunk" << suffix(j) << " code (by omega) h\n";
    f << "  exact obstructionChunk" << suffix(chunks-1) << " code (by omega) (by omega)\n\n"
      << "theorem regularVector_regular (g : H) (hg : g • regularVector = regularVector) : g = 1 := by\n"
      << "  obtain ⟨i, rfl⟩ := groupElement_surjective g\n";
    for(int j=0;j<17;++j)
      f << "  by_cases h : i.val < " << 64*(j+1) << "\n"
        << "  · exact regularChunk" << suffix(j) << " i (by omega) h hg\n";
    f << "  exact regularChunk017 i (by omega) (by omega) hg\n\n"
      << "theorem no_simultaneous_regular (v : V) :\n"
      << "    (∃ g : H, g ≠ 1 ∧ g • v = v) ∨\n"
      << "      (∃ g : H, g ≠ 1 ∧ g • (v - hole) = v - hole) := by\n"
      << "  obtain ⟨w, hw⟩ := obstruction_checked ⟨vectorCode v, vectorCode_lt v⟩\n"
      << "  simpa only [vector_vectorCode] using obstructionCheck_sound hw\n\n"
      << "end Kourovka.P21_29\n";
    std::cout << "Generated 19683 obstruction witnesses and 1152 regular-vector checks in "
              << chunks+18 << " bounded shards.\n";
  } catch (const std::exception &e) { std::cerr << e.what() << '\n'; return 1; }
}
