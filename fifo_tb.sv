module fifo_tb;

  logic clk, rst_n, wr_en, rd_en;
  logic [7:0] data_in, data_out;
  logic full, empty;

  fifo dut (
    .clk(clk), .rst_n(rst_n),
    .wr_en(wr_en), .rd_en(rd_en),
    .data_in(data_in), .data_out(data_out),
    .full(full), .empty(empty)
  );

  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;

  // Stimulus
  initial begin
    rst_n = 0; wr_en = 0; rd_en = 0; data_in = 0;
    #12 rst_n = 1;
    repeat (5) begin
      @(posedge clk);
      wr_en = 1;
      data_in = $urandom;
    end
    wr_en = 0;
    repeat (5) begin
      @(posedge clk);
      rd_en = 1;
    end
    $finish;
  end

  // Assertions
  property no_write_when_full;
    @(posedge clk) disable iff (!rst_n)
    full |-> !wr_en;
  endproperty
  assert property (no_write_when_full);

  property no_read_when_empty;
    @(posedge clk) disable iff (!rst_n)
    empty |-> !rd_en;
  endproperty
  assert property (no_read_when_empty);

endmodule