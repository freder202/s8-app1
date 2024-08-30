---------------------------------------------------------------------------------------------
--	Author :    Marc-Andre Tetrault
--  Project :   Verification Primer
--
--  Universite de Sherbrooke, 2017
---------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------
--	Library and Package Declarations
---------------------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.numeric_std.ALL;

---------------------------------------------------------------------------------------------
--	Entity Declaration
---------------------------------------------------------------------------------------------
entity SerialTransmitter is
port(
	reset					: in std_logic;
	clk						: in std_logic;
	i_pdata					: in std_logic_vector(15 downto 0);
	i_pdata_load			: in std_logic;
	o_engineready_loadack	: out std_logic;  -- ready when high, ack_tx/busy when low
	o_serialdata			: out std_logic
	);
end SerialTransmitter;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of SerialTransmitter is

--	Components

--	User types and State Machines

--	Convenient constants
constant c_BitLength_integer	: integer := 16;
constant c_BitLength_vector		: unsigned(5 downto 0) :=  to_unsigned(c_BitLength_integer + 1, 6);	-- add parity bit, includes stop bit

constant c_InitEvenParity		: std_logic := '0';
constant c_InitOddParity		: std_logic := '1';

--	Signals
signal reset_local		: std_logic;

--	Registers
signal q_PData_Load			: std_logic;
signal q_SerialOutput		: std_logic;
signal q_OutputShaper		: std_logic;
signal q_EngineReady_LoadAck		: std_logic;
signal q_DownCounter		: unsigned(5 downto 0) := (others => '0');

signal q_Serialiser		: std_logic_vector(c_BitLength_integer - 1 downto 0);

signal q_ParityCount		: std_logic;

-- Attributes

begin

----------------------------------------
--	Asynchronous reset with synch release
--	for system reset
----------------------------------------
LocalResetGen : block
	signal q_ResetFilter	: std_logic_vector(1 downto 0);
begin
	process (reset, clk)
	begin
		if (reset = '1') then
			q_ResetFilter <= "00";
		elsif (clk'event and clk = '1') then
			q_ResetFilter(0) <= '1';
			q_ResetFilter(1) <= q_ResetFilter(0);
		end if;
	end process;

	reset_local <= q_ResetFilter(1);
end block;

----------------------------------------
--	Input line buffering and
--	Start Bit Detection
----------------------------------------
MainProcess : process(clk)
begin
	if (clk'event and clk = '1')then

		-- 50% phase clock change, treat as asynch clock for propagation delays in design
		if(reset_local = '0') then
			q_PData_Load <= '0';
		else
			q_PData_Load <= i_pdata_load;
		end if;

		if(reset_local = '0' or (q_EngineReady_LoadAck = '0' and q_DownCounter = "000000")) then
			q_EngineReady_LoadAck <= '1';
		elsif(i_pdata_load = '1' and q_EngineReady_LoadAck = '1') then
			q_EngineReady_LoadAck <= '0';
		end if;

		-- Load data on proper synch, else always shift by padding with '1'
		-- which acts as stop bit and "wait" state
		if(reset_local = '0') then
			q_Serialiser <= (others => '1');
		elsif(i_pdata_load = '1' and q_EngineReady_LoadAck = '1') then
			q_Serialiser <= i_pdata;
		else
			q_Serialiser <= '1' & q_Serialiser(c_BitLength_integer - 1 downto 1);
		end if;

		if(q_DownCounter = "000000") then
			q_ParityCount	<= c_InitOddParity;
		else
			q_ParityCount <= q_ParityCount xor q_Serialiser(0);
		end if;


		-- if transmission is active, decrement by 1
		if(reset_local = '0') then
			q_DownCounter <= "000000";
		elsif(q_DownCounter /= "000000") then
			q_DownCounter <= q_DownCounter - 1;
		-- Down counter process
		elsif(i_pdata_load = '1' and q_EngineReady_LoadAck = '1') then
			q_DownCounter <= c_BitLength_vector;
		else
	  		null; -- do nothing
		end if;

		-- Start bit generation and single file line to
		-- falling edge domain
		if(i_pdata_load = '1' and q_EngineReady_LoadAck = '1') then
			q_OutputShaper <= '0';
		elsif(q_DownCounter = "000001") then
			q_OutputShaper <= q_ParityCount;
		else
			q_OutputShaper <= q_Serialiser(0);
		end if;

	end if;
end process;

----------------------------------------
--	Change clock phase only
--	no logic put here, none needed
--	Needs special timing constraint to
--	half the clock period
--	Does it need stronger gate to drive pad and PCB trace? No, LVDS buffer
----------------------------------------
OutputBuffer : process(clk)
begin
	if (clk'event and clk = '1')then
		if(reset_local = '0') then
			q_SerialOutput <= '1';
		else
			q_SerialOutput <= q_OutputShaper;
		end if;
	end if;
end process;



o_serialdata <= q_SerialOutput;
o_engineready_loadack	<= q_EngineReady_LoadAck;


end Behavioral;
