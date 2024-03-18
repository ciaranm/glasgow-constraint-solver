#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_MINIZINC_FLATZINC_JSON_PARSER_CONSTRAINT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_MINIZINC_FLATZINC_JSON_PARSER_CONSTRAINT_HH

// Generated using https://app.quicktype.io/ from https://www.minizinc.org/schemas/fznjson/

#include <nlohmann/json.hpp>
#include <optional>
#include <variant>

#ifndef NLOHMANN_OPT_HELPER
#define NLOHMANN_OPT_HELPER
namespace nlohmann
{
    template <typename T>
    struct adl_serializer<std::shared_ptr<T>>
    {
        static void to_json(json & j, const std::shared_ptr<T> & opt)
        {
            if (! opt)
                j = nullptr;
            else
                j = *opt;
        }

        static std::shared_ptr<T> from_json(const json & j)
        {
            if (j.is_null())
                return std::make_shared<T>();
            else
                return std::make_shared<T>(j.get<T>());
        }
    };
    template <typename T>
    struct adl_serializer<std::optional<T>>
    {
        static void to_json(json & j, const std::optional<T> & opt)
        {
            if (! opt)
                j = nullptr;
            else
                j = *opt;
        }

        static std::optional<T> from_json(const json & j)
        {
            if (j.is_null())
                return std::make_optional<T>();
            else
                return std::make_optional<T>(j.get<T>());
        }
    };
}
#endif

namespace gcs
{
    namespace flatzincjson
    {
        using nlohmann::json;

#ifndef NLOHMANN_UNTYPED_gcs_flatzincjson_HELPER
#define NLOHMANN_UNTYPED_gcs_flatzincjson_HELPER
        inline json get_untyped(const json & j, const char * property)
        {
            if (j.find(property) != j.end()) {
                return j.at(property).get<json>();
            }
            return json();
        }

        inline json get_untyped(const json & j, std::string property)
        {
            return get_untyped(j, property.data());
        }
#endif

#ifndef NLOHMANN_OPTIONAL_gcs_flatzincjson_HELPER
#define NLOHMANN_OPTIONAL_gcs_flatzincjson_HELPER
        template <typename T>
        inline std::shared_ptr<T> get_heap_optional(const json & j, const char * property)
        {
            auto it = j.find(property);
            if (it != j.end() && ! it->is_null()) {
                return j.at(property).get<std::shared_ptr<T>>();
            }
            return std::shared_ptr<T>();
        }

        template <typename T>
        inline std::shared_ptr<T> get_heap_optional(const json & j, std::string property)
        {
            return get_heap_optional<T>(j, property.data());
        }
        template <typename T>
        inline std::optional<T> get_stack_optional(const json & j, const char * property)
        {
            auto it = j.find(property);
            if (it != j.end() && ! it->is_null()) {
                return j.at(property).get<std::optional<T>>();
            }
            return std::optional<T>();
        }

        template <typename T>
        inline std::optional<T> get_stack_optional(const json & j, std::string property)
        {
            return get_stack_optional<T>(j, property.data());
        }
#endif

        struct ObjectiveClass
        {
            std::optional<std::vector<std::vector<double>>> set;
            std::optional<std::string> string;
        };

        using FlatZincJso = std::variant<bool, ObjectiveClass, double, std::string>;

        struct PurpleFlatZincJso
        {
            std::optional<std::vector<std::vector<double>>> set;
            std::optional<std::string> string;
        };

        using ConstraintArg = std::variant<std::vector<FlatZincJso>, bool, PurpleFlatZincJso, double, std::string>;

        struct ConstraintElement;

        using AnnUnion = std::variant<std::shared_ptr<ConstraintElement>, std::string>;

        struct ConstraintElement
        {
            std::optional<std::vector<AnnUnion>> ann;
            std::vector<ConstraintArg> args;
            std::string id;
        };

        enum class Method : int
        {
            MAXIMIZE,
            MINIMIZE,
            SATISFY
        };

        struct Solve
        {
            std::optional<std::vector<AnnUnion>> ann;
            Method method;
            std::optional<FlatZincJso> objective;
        };

        /**
         * A JSON representation of a FlatZinc model
         */
        struct FlatZincJson
        {
            std::map<std::string, nlohmann::json> arrays;
            std::vector<ConstraintElement> constraints;
            std::vector<std::string> output;
            Solve solve;
            std::map<std::string, nlohmann::json> variables;
            std::string version;
        };
    }
}

namespace gcs
{
    namespace flatzincjson
    {
        void from_json(const json & j, ObjectiveClass & x);
        void to_json(json & j, const ObjectiveClass & x);

        void from_json(const json & j, PurpleFlatZincJso & x);
        void to_json(json & j, const PurpleFlatZincJso & x);

        void from_json(const json & j, ConstraintElement & x);
        void to_json(json & j, const ConstraintElement & x);

        void from_json(const json & j, Solve & x);
        void to_json(json & j, const Solve & x);

        void from_json(const json & j, FlatZincJson & x);
        void to_json(json & j, const FlatZincJson & x);

        void from_json(const json & j, Method & x);
        void to_json(json & j, const Method & x);
    }
}
namespace nlohmann
{
    template <>
    struct adl_serializer<std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string>>
    {
        static void from_json(const json & j, std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string> & x);
        static void to_json(json & j, const std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string> & x);
    };

    template <>
    struct adl_serializer<std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string>>
    {
        static void from_json(const json & j, std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string> & x);
        static void to_json(json & j, const std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string> & x);
    };

    template <>
    struct adl_serializer<std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string>>
    {
        static void from_json(const json & j, std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string> & x);
        static void to_json(json & j, const std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string> & x);
    };
}
namespace gcs
{
    namespace flatzincjson
    {
        inline void from_json(const json & j, ObjectiveClass & x)
        {
            x.set = get_stack_optional<std::vector<std::vector<double>>>(j, "set");
            x.string = get_stack_optional<std::string>(j, "string");
        }

        inline void to_json(json & j, const ObjectiveClass & x)
        {
            j = json::object();
            j["set"] = x.set;
            j["string"] = x.string;
        }

        inline void from_json(const json & j, PurpleFlatZincJso & x)
        {
            x.set = get_stack_optional<std::vector<std::vector<double>>>(j, "set");
            x.string = get_stack_optional<std::string>(j, "string");
        }

        inline void to_json(json & j, const PurpleFlatZincJso & x)
        {
            j = json::object();
            j["set"] = x.set;
            j["string"] = x.string;
        }

        inline void from_json(const json & j, ConstraintElement & x)
        {
            x.ann = get_stack_optional<std::vector<AnnUnion>>(j, "ann");
            x.args = j.at("args").get<std::vector<ConstraintArg>>();
            x.id = j.at("id").get<std::string>();
        }

        inline void to_json(json & j, const ConstraintElement & x)
        {
            j = json::object();
            j["ann"] = x.ann;
            j["args"] = x.args;
            j["id"] = x.id;
        }

        inline void from_json(const json & j, Solve & x)
        {
            x.ann = get_stack_optional<std::vector<AnnUnion>>(j, "ann");
            x.method = j.at("method").get<Method>();
            x.objective = get_stack_optional<std::variant<bool, ObjectiveClass, double, std::string>>(j, "objective");
        }

        inline void to_json(json & j, const Solve & x)
        {
            j = json::object();
            j["ann"] = x.ann;
            j["method"] = x.method;
            j["objective"] = x.objective;
        }

        inline void from_json(const json & j, FlatZincJson & x)
        {
            x.arrays = j.at("arrays").get<std::map<std::string, nlohmann::json>>();
            x.constraints = j.at("constraints").get<std::vector<ConstraintElement>>();
            x.output = j.at("output").get<std::vector<std::string>>();
            x.solve = j.at("solve").get<Solve>();
            x.variables = j.at("variables").get<std::map<std::string, nlohmann::json>>();
            x.version = j.at("version").get<std::string>();
        }

        inline void to_json(json & j, const FlatZincJson & x)
        {
            j = json::object();
            j["arrays"] = x.arrays;
            j["constraints"] = x.constraints;
            j["output"] = x.output;
            j["solve"] = x.solve;
            j["variables"] = x.variables;
            j["version"] = x.version;
        }

        inline void from_json(const json & j, Method & x)
        {
            if (j == "maximize")
                x = Method::MAXIMIZE;
            else if (j == "minimize")
                x = Method::MINIMIZE;
            else if (j == "satisfy")
                x = Method::SATISFY;
            else {
                throw std::runtime_error("Input JSON does not conform to schema!");
            }
        }

        inline void to_json(json & j, const Method & x)
        {
            switch (x) {
            case Method::MAXIMIZE: j = "maximize"; break;
            case Method::MINIMIZE: j = "minimize"; break;
            case Method::SATISFY: j = "satisfy"; break;
            default: throw std::runtime_error("This should not happen");
            }
        }
    }
}
namespace nlohmann
{
    inline void adl_serializer<std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string>>::from_json(const json & j, std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string> & x)
    {
        if (j.is_boolean())
            x = j.get<bool>();
        else if (j.is_number())
            x = j.get<double>();
        else if (j.is_string())
            x = j.get<std::string>();
        else if (j.is_object())
            x = j.get<gcs::flatzincjson::ObjectiveClass>();
        else
            throw std::runtime_error("Could not deserialise!");
    }

    inline void adl_serializer<std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string>>::to_json(json & j, const std::variant<bool, gcs::flatzincjson::ObjectiveClass, double, std::string> & x)
    {
        switch (x.index()) {
        case 0:
            j = std::get<bool>(x);
            break;
        case 1:
            j = std::get<gcs::flatzincjson::ObjectiveClass>(x);
            break;
        case 2:
            j = std::get<double>(x);
            break;
        case 3:
            j = std::get<std::string>(x);
            break;
        default: throw std::runtime_error("Input JSON does not conform to schema!");
        }
    }

    inline void adl_serializer<std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string>>::from_json(const json & j, std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string> & x)
    {
        if (j.is_boolean())
            x = j.get<bool>();
        else if (j.is_number())
            x = j.get<double>();
        else if (j.is_string())
            x = j.get<std::string>();
        else if (j.is_object())
            x = j.get<gcs::flatzincjson::PurpleFlatZincJso>();
        else if (j.is_array())
            x = j.get<std::vector<gcs::flatzincjson::FlatZincJso>>();
        else
            throw std::runtime_error("Could not deserialise!");
    }

    inline void adl_serializer<std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string>>::to_json(json & j, const std::variant<std::vector<gcs::flatzincjson::FlatZincJso>, bool, gcs::flatzincjson::PurpleFlatZincJso, double, std::string> & x)
    {
        switch (x.index()) {
        case 0:
            j = std::get<std::vector<gcs::flatzincjson::FlatZincJso>>(x);
            break;
        case 1:
            j = std::get<bool>(x);
            break;
        case 2:
            j = std::get<gcs::flatzincjson::PurpleFlatZincJso>(x);
            break;
        case 3:
            j = std::get<double>(x);
            break;
        case 4:
            j = std::get<std::string>(x);
            break;
        default: throw std::runtime_error("Input JSON does not conform to schema!");
        }
    }

    inline void adl_serializer<std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string>>::from_json(const json & j, std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string> & x)
    {
        if (j.is_string())
            x = j.get<std::string>();
        else if (j.is_object())
            x = j.get<std::shared_ptr<gcs::flatzincjson::ConstraintElement>>();
        else
            throw std::runtime_error("Could not deserialise!");
    }

    inline void adl_serializer<std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string>>::to_json(json & j, const std::variant<std::shared_ptr<gcs::flatzincjson::ConstraintElement>, std::string> & x)
    {
        switch (x.index()) {
        case 0:
            j = std::get<std::shared_ptr<gcs::flatzincjson::ConstraintElement>>(x);
            break;
        case 1:
            j = std::get<std::string>(x);
            break;
        default: throw std::runtime_error("Input JSON does not conform to schema!");
        }
    }
}

#endif
