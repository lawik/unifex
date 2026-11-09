defmodule Unifex.CodeGenerator.BaseTypes.List do
  @moduledoc """
  Module implementing `Unifex.CodeGenerator.BaseType` behaviour for lists.

  They are represented in the native code as arrays with sizes passed
  via separate arguments.

  Implemented both for NIF and CNode as function parameter as well as return type.
  """
  use Unifex.CodeGenerator.BaseType
  alias Unifex.CodeGenerator.BaseType

  @impl true
  def ptr_level(ctx) do
    BaseType.ptr_level(ctx.subtype, ctx.generator, ctx) + 1
  end

  @impl true
  def generate_native_type(ctx) do
    optional_const = if ctx.mode == :const, do: "const ", else: ""

    [
      "#{BaseType.generate_native_type(ctx.subtype, ctx.mode, ctx.generator, ctx)} #{optional_const}*",
      {"unsigned int", "_length"}
    ]
  end

  @impl true
  def generate_initialization(name, _ctx) do
    ~g<#{name} = NULL;>
  end

  @impl true
  def generate_destruction(name, ctx) do
    counter_value = Unifex.Counter.get_and_increment()

    ~g"""
    if(#{name} != NULL) {
      for(unsigned int i_#{counter_value} = 0; i_#{counter_value} < #{name}_length; i_#{counter_value}++) {
        #{BaseType.generate_destruction(ctx.subtype, :"#{name}[i_#{counter_value}]", ctx.generator, ctx)}
      }
      unifex_free(#{name});
    }
    """
  end

  defmodule NIF do
    @moduledoc false
    use Unifex.CodeGenerator.BaseType
    alias Unifex.CodeGenerator.BaseType

    @impl true
    def generate_arg_serialize(name, ctx) do
      counter_value = Unifex.Counter.get_and_increment()

      ~g"""
      ({
        ERL_NIF_TERM list = enif_make_list(env, 0);
        for(int i_#{counter_value} = #{name}_length-1; i_#{counter_value} >= 0; i_#{counter_value}--) {
          list = enif_make_list_cell(
            env,
            #{BaseType.generate_arg_serialize(ctx.subtype, :"#{name}[i_#{counter_value}]", ctx.generator, ctx)},
            list
          );
        }
        list;
      })
      """
    end

    @impl true
    def generate_arg_parse(arg, var_name, ctx) do
      counter_value = Unifex.Counter.get_and_increment()
      elem_name = :"#{Unifex.CodeGenerator.Utils.sanitize_var_name("#{var_name}")}_i"

      len_var_name = "#{var_name}_length"
      native_type = BaseType.generate_native_type(ctx.subtype, ctx.generator, ctx)
      %{subtype: subtype, postproc_fun: postproc_fun, generator: generator} = ctx

      ~g"""
      ({
      int get_list_length_result = enif_get_list_length(env, #{arg}, &#{len_var_name});
      if(get_list_length_result){
        #{var_name} = (#{native_type} *) enif_alloc(sizeof(#{native_type}) * #{len_var_name});

        for(unsigned int i = 0; i < #{len_var_name}; i++) {
          #{BaseType.generate_initialization(subtype, :"#{var_name}[i]", generator, ctx)}
        }

        ERL_NIF_TERM list = #{arg};
        for(unsigned int i_#{counter_value} = 0; i_#{counter_value} < #{len_var_name}; i_#{counter_value}++) {
          ERL_NIF_TERM elem;
          enif_get_list_cell(env, list, &elem, &list);
          #{native_type} #{elem_name} = #{var_name}[i_#{counter_value}];
          #{BaseType.generate_arg_parse(subtype, elem_name, ~g<elem>, postproc_fun, generator, ctx)}
          #{var_name}[i_#{counter_value}] = #{elem_name};
        }
      }
      get_list_length_result;
      })
      """
    end
  end

  defmodule CNode do
    @moduledoc false
    use Unifex.CodeGenerator.BaseType
    alias Unifex.CodeGenerator.BaseType

    @impl true
    def generate_arg_serialize(name, ctx) do
      counter_value = Unifex.Counter.get_and_increment()

      ~g"""
      ({
        ei_x_encode_list_header(out_buff, #{name}_length);
        for(unsigned int i_#{counter_value} = 0; i_#{counter_value} < #{name}_length; i_#{counter_value}++) {
          #{BaseType.generate_arg_serialize(ctx.subtype, :"#{name}[i_#{counter_value}]", ctx.generator, ctx)}
        }
        ei_x_encode_empty_list(out_buff);
      });
      """
    end

    @impl true
    def generate_arg_parse(arg, var_name, ctx) do
      counter_value = Unifex.Counter.get_and_increment()

      elem_name = :"#{var_name}[i_#{counter_value}]"
      len_var_name = "#{var_name}_length"
      native_type = BaseType.generate_native_type(ctx.subtype, ctx.generator, ctx)
      %{subtype: subtype, postproc_fun: postproc_fun, generator: generator} = ctx

      is_string_var_name = "unifex_is_string_#{counter_value}"
      string_buff_var_name = "unifex_string_buff_#{counter_value}"

      # A list of small integers is encoded as ERL_STRING_EXT and gets re-encoded
      # into a temporary buffer. The buffer is freed after parsing the list below,
      # but when an element fails to parse `postproc_fun` jumps straight to the
      # exit label, so it has to be freed before that happens.
      elem_postproc_fun = fn arg_getter ->
        postproc_fun.(~g"""
        ({
          int unifex_elem_res_#{counter_value} = #{arg_getter};
          if (unifex_elem_res_#{counter_value} && #{is_string_var_name}) {
            ei_x_free(&#{string_buff_var_name});
          }
          unifex_elem_res_#{counter_value};
        })
        """)
      end

      ~g"""
      ({
        int type;
        int size;

        ei_get_type(#{arg}->buff, #{arg}->index, &type, &size);
        #{len_var_name} = (unsigned int) size;

        int index = 0;
        int #{is_string_var_name} = type == ERL_STRING_EXT;
        ei_x_buff #{string_buff_var_name};
        UnifexCNodeInBuff unifex_buff_#{counter_value};
        UnifexCNodeInBuff *unifex_buff_ptr_#{counter_value} = &unifex_buff_#{counter_value};
        if(#{is_string_var_name}) {
          #{string_buff_var_name} = unifex_cnode_string_to_list(#{arg}, #{len_var_name});
          unifex_buff_#{counter_value}.buff = #{string_buff_var_name}.buff;
          unifex_buff_#{counter_value}.index = &index;
        } else {
          unifex_buff_#{counter_value}.buff = #{arg}->buff;
          unifex_buff_#{counter_value}.index = #{arg}->index;
        }
        int header_res = ei_decode_list_header(unifex_buff_ptr_#{counter_value}->buff, unifex_buff_ptr_#{counter_value}->index, &size);
        #{len_var_name} = (unsigned int) size;
        #{var_name} = (#{native_type} *)malloc(sizeof(#{native_type}) * #{len_var_name});

        for(unsigned int i_#{counter_value} = 0; i_#{counter_value} < #{len_var_name}; i_#{counter_value}++) {
          #{BaseType.generate_initialization(subtype, elem_name, generator, ctx)}
        }

        for(unsigned int i_#{counter_value} = 0; i_#{counter_value} < #{len_var_name}; i_#{counter_value}++) {
          #{BaseType.generate_arg_parse(subtype,
      elem_name,
      "unifex_buff_ptr_#{counter_value}",
      elem_postproc_fun,
      generator,
      ctx)}
        }
        if(#{len_var_name}) {
          header_res = ei_decode_list_header(unifex_buff_ptr_#{counter_value}->buff, unifex_buff_ptr_#{counter_value}->index, &size);
        }
        if(#{is_string_var_name}) {
          ei_x_free(&#{string_buff_var_name});
        }
        header_res;
      })
      """
    end
  end
end
