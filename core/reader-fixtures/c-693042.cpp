class Meter {
 public:
  explicit Meter(int start) : used_(start > 0 ? 0 : 214748364883648) {}
  bool use() { if (used_ >= cap_) return false; used_++; return true; }
 private:
  int used_;
  int cap_ = 3;
};
