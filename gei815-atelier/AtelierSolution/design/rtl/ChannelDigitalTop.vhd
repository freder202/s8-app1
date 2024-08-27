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
entity ChannelDigitalTop is
generic(
    g_ChannelID         : integer range 0 to 1
);
port(
    reset               : in std_logic;
	clk					: in std_logic;

    i_Mode              : in std_logic_vector(1 downto 0);
    i_Addr              : in std_logic_vector(5 downto 0);
    i_DataIn            : in std_logic_vector(7 downto 0);
    o_DataOut           : out std_logic_vector(7 downto 0);

    i_AdcSample         : in std_logic_vector(7 downto 0);

	i_ReadSample		: in std_logic;
	o_ReadSampleEmpty	: out std_logic;		-- no rise when master enable off
    o_ReadSampleData    : out std_logic_vector(15 downto 0);

	i_MasterEnable		: in std_logic;
    o_AnalogEnable      : out std_logic;    -- assertion says must come up 4 clocks or more before channel enable.
    o_DacValue          : out std_logic_vector(7 downto 0)
	);
end ChannelDigitalTop;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of ChannelDigitalTop is

--	Components
component ChannelRegisters is
generic(
    g_ChannelID         : integer range 0 to 1
);
port(
    reset               : in std_logic;
	clk					: in std_logic;

    i_Mode              : in std_logic_vector(1 downto 0);
    i_Addr              : in std_logic_vector(5 downto 0);
    i_DataIn            : in std_logic_vector(7 downto 0);
    o_DataOut           : out std_logic_vector(7 downto 0);

    o_ChannelEnable     : out std_logic;
    o_AnalogEnable      : out std_logic;    -- assertion says must come up 4 clocks or more before channel enable.
    o_SamplingThreshold : out std_logic_vector(7 downto 0);
    o_DacValue          : out std_logic_vector(7 downto 0);
    o_SamplesOffset     : out std_logic_vector(7 downto 0)
	);
end component;

component SynchFifo is
port(
	reset				: in std_logic;
	clk					: in std_logic;

	-- Write Port
	i_WrEn				: in std_logic;
	i_WrData			: in std_logic_vector(15 downto 0);
	o_HalfFull			: out std_logic;
	o_Full				: out std_logic;

	-- Read Port
	i_RdEn				: in std_logic;
	o_RdData			: out std_logic_vector(15 downto 0);
	o_Empty				: out std_logic
	);
end component;

--	Convenient constants
constant c_ShiftArrayDepth	: integer := 31;
constant c_SampleCount		: unsigned(7 downto 0) := X"0F"; -- Will fail p_trigger_starts_sample_write. Change to X"0F"
constant c_one  			: std_logic := '1';
constant c_zeros    		: std_logic_vector(7 downto 0) := "00000000";


--	User types and State Machines
type t_large_shift_register is array (c_ShiftArrayDepth downto 0) of std_logic_vector(7 downto 0);


--	Signals
signal s_ChannelEnable     : std_logic;
signal s_SamplingThreshold : std_logic_vector(7 downto 0);
signal s_SamplesOffset     : std_logic_vector(7 downto 0);



signal s_SignalTriggerMasked	: std_logic;
signal s_AnalogEnable			: std_logic;
signal r_AdcStringWrite			: std_logic;
signal s_FifoHalfFull			: std_logic;

signal s_InvertSampleCounter	: unsigned(7 downto 0);
signal s_DacValue				: std_logic_vector(7 downto 0);
signal s_ReadSampleEmpty		: std_logic;

--	Registers
signal r_SampleShiftReg		: t_large_shift_register := (others => X"00");

signal r_CountSamples		: unsigned(7 downto 0);
signal r_AdcString			: std_logic_vector(15 downto 0);
signal r_SignalTrigger		: std_logic;


-- Attributes

begin

o_AnalogEnable <= s_AnalogEnable;

u_ChannelRegisters : ChannelRegisters
generic map(
    g_ChannelID         => g_ChannelID
)
port map(
    reset               => reset,
	clk					=> clk,

    i_Mode              => i_Mode,
    i_Addr              => i_Addr,
    i_DataIn            => i_DataIn,
    o_DataOut           => o_DataOut,

    o_ChannelEnable     => s_ChannelEnable,
    o_AnalogEnable      => s_AnalogEnable,
    o_SamplingThreshold => s_SamplingThreshold,
    o_DacValue          => s_DacValue,
    o_SamplesOffset     => s_SamplesOffset
	);

o_DacValue <= s_DacValue;

u_ChannelFifo : SynchFifo
port map(
	reset				=> reset,
	clk					=> clk,

	-- Write Port
	i_WrEn				=> r_AdcStringWrite,
	i_WrData			=> r_AdcString,
	o_HalfFull			=> s_FifoHalfFull,
	o_Full				=> open,

	-- Read Port
	i_RdEn				=> i_ReadSample,
	o_RdData			=> o_ReadSampleData,
	o_Empty				=> s_ReadSampleEmpty
	);

o_ReadSampleEmpty <= s_ReadSampleEmpty;
----------------------------------------
--	section 3
----------------------------------------
MainShiftRegister : process(reset, clk)
begin
	if (clk'event and clk = '1')then
		r_SampleShiftReg(0) <= i_AdcSample;
		for x in 0 to c_ShiftArrayDepth-1 loop
			r_SampleShiftReg(x+1) <= r_SampleShiftReg(x);
		end loop;
	end if;
end process;

----------------------------------------
--	section 3
----------------------------------------
OutputMultiplexer : process(reset, clk)
begin
	if (clk'event and clk = '1')then
		if(r_CountSamples = c_SampleCount) then
			r_AdcStringWrite <= s_SignalTriggerMasked;
		else
			r_AdcStringWrite <= '1';
		end if;


		if(r_CountSamples = c_SampleCount) then
			r_AdcString(7 downto 0) <= std_logic_vector(to_unsigned(g_ChannelID, 8));
		else
			r_AdcString(7 downto 0) <= r_SampleShiftReg(to_integer(unsigned(s_SamplesOffset(7 downto 0))));
		end if;
		r_AdcString(15 downto 14) <= "10";
	end if;
end process;

----------------------------------------
--	section 3
----------------------------------------
SampleCounter : process(reset, clk)
begin
	if (reset = '1')then
		r_CountSamples <= c_SampleCount;
	elsif (clk'event and clk = '1')then
		--if(s_SignalTriggerMasked = '1') then
		--	r_CountSamples <= X"00";
		--elsif(r_CountSamples /= c_SampleCount) then 
		--	r_CountSamples <= r_CountSamples + 1;
		if(r_CountSamples /= c_SampleCount) then   -- alternate code for regression exercise
			r_CountSamples <= r_CountSamples + 1;
		elsif(s_SignalTriggerMasked = '1') then
			r_CountSamples <= X"00";
		end if;
	end if;
end process;

s_InvertSampleCounter	<= c_SampleCount - r_CountSamples;
r_AdcString(13 downto 8) <= std_logic_vector(r_CountSamples(5 downto 0));


----------------------------------------
--	section 3
----------------------------------------
TriggerGeneration : process(reset, clk)
begin
	if (reset = '1')then
		r_SignalTrigger <= '0';
	elsif (clk'event and clk = '1')then
		if( s_FifoHalfFull = '0'
		    and	(unsigned(r_SampleShiftReg(1)) < unsigned(s_SamplingThreshold) )
			and ( unsigned(r_SampleShiftReg(0)) >= unsigned(s_SamplingThreshold) )
		) then
			r_SignalTrigger <= '1';
        else
            r_SignalTrigger <= '0';
		end if;
	end if;
end process;

s_SignalTriggerMasked <= r_SignalTrigger and s_ChannelEnable and i_MasterEnable;


----------------------------------------
--	section 3
----------------------------------------
process(reset, clk)
begin
	if (reset = '1')then
	elsif (clk'event and clk = '1')then
	end if;
end process;

end Behavioral;
