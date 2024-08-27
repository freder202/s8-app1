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
entity ChannelRegisters is
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
end ChannelRegisters;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of ChannelRegisters is

--	Components

--	User types and State Machines

--	Convenient constants
constant c_one  : std_logic := '1';
constant c_zeros    : std_logic_vector(7 downto 0) := "00000000";

--	Signals

--	Registers
signal r_ChannelEnable     : std_logic;
signal r_AnalogEnable      : std_logic;
signal r_SamplingThreshold : std_logic_vector(7 downto 0);
signal r_DacValue          : std_logic_vector(7 downto 0);
signal r_SamplesOffset     : std_logic_vector(7 downto 0);

-- Attributes

begin

-- read process
process(reset, clk)
begin
	if (clk'event and clk = '1')then
        case i_Addr(3 downto 0) is
            when X"1" =>
				o_DataOut(7 downto 1) <= (others => '0');
                o_DataOut(0) <= r_AnalogEnable;

            when X"2" =>
                o_DataOut <= r_SamplingThreshold;

            when X"3" =>
                o_DataOut <= r_DacValue;

            when X"4" =>
                o_DataOut <= r_SamplesOffset;

            when others => -- or 0
				o_DataOut(7 downto 1) <= (others => '0');
                o_DataOut(0) <= r_ChannelEnable;
        end case;

	end if;
end process;


-- write process
process(reset, clk)
begin
	if (reset = '1')then

        r_ChannelEnable     <= '0';
        r_AnalogEnable      <= '0';
        r_SamplingThreshold <= X"00";
        r_DacValue          <= X"00";
        r_SamplesOffset     <= X"00";

	elsif (clk'event and clk = '1')then
        if(i_Mode = "01" and i_Addr(5 downto 4) = std_logic_vector(to_unsigned(g_ChannelID, 2)) ) then
            case i_Addr(3 downto 0) is
                when X"0" =>
                    r_ChannelEnable     <= i_DataIn(0);

                when X"1" =>
                    r_AnalogEnable      <= i_DataIn(0);

                when X"2" =>
                    r_SamplingThreshold <= i_DataIn;

                when X"3" =>
                    r_DacValue <= i_DataIn;

                when X"4" =>
                    r_SamplesOffset <= i_DataIn;

                when others =>
                    null;
                    --todo set sticky error bit
            end case;
        end if;
	end if;
end process;


o_ChannelEnable     <= r_ChannelEnable;
o_AnalogEnable      <= r_AnalogEnable;
o_SamplingThreshold <= r_SamplingThreshold;
o_DacValue          <= r_DacValue;
o_SamplesOffset     <= r_SamplesOffset;


end Behavioral;
