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
entity CommonRegisters is
port(
    reset               : in std_logic;
	clk					: in std_logic;

    i_Mode              : in std_logic_vector(1 downto 0);
    i_Addr              : in std_logic_vector(5 downto 0);
    i_DataIn            : in std_logic_vector(7 downto 0);
    o_DataOut           : out std_logic_vector(7 downto 0);

    o_MasterEnable      : out std_logic;
    o_DebugWaveOutput   : out std_logic
	);
end CommonRegisters;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of CommonRegisters is

--	Components

--	User types and State Machines

--	Convenient constants
constant c_one  : std_logic := '1';
constant c_zeros    : std_logic_vector(7 downto 0) := "00000000";

--	Signals

--	Registers
signal r_MasterEnable     : std_logic;
signal r_DebugWaveOutput  : std_logic;

-- Attributes

begin

-- read process
process(reset, clk)
begin
	if (clk'event and clk = '1')then
        case i_Addr(3 downto 0) is
            when X"1" =>
                o_DataOut(0) <= r_DebugWaveOutput;
				o_DataOut(7 downto 1) <= (others => '0');

            when others => -- or 0
                o_DataOut(0) <= r_MasterEnable;
				o_DataOut(7 downto 1) <= (others => '0');
        end case;

	end if;
end process;


-- write process
process(reset, clk)
begin
	if (reset = '1')then

        r_MasterEnable     <= '0';
        r_DebugWaveOutput      <= '0';

	elsif (clk'event and clk = '1')then
        if(i_Mode = "01" and i_Addr(5 downto 4) = std_logic_vector(to_unsigned(2, 2)) ) then
            case i_Addr(3 downto 0) is
                when X"0" =>
                    r_MasterEnable      <= i_DataIn(0);

                when X"1" =>
                    r_DebugWaveOutput   <= i_DataIn(0);

                when others =>
                    null;
                    --todo set sticky error bit
            end case;
        end if;
	end if;
end process;


o_MasterEnable      <= r_MasterEnable;
o_DebugWaveOutput   <= r_DebugWaveOutput;



end Behavioral;
